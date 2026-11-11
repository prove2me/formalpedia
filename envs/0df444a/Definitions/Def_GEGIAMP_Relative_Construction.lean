-- Prove2me | Definitions.Def_GEGIAMP_Relative_Construction
-- name    : GEGIAMP_Relative_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:52:40.33261+00:00
-- url     : https://prove2.me/theorems/b533bab0-d377-485d-85e4-169d34e182d0
-- title:
--   The grouped query construction of GEG-IAMP, its proof-only final query, sequential rounding and the randomness
-- statement:
--   For fixed deterministic normalization factors $\omega$: the residual and query rule (6.12) with the zero-residual rule ($i^*=\min\{j:(P_{s-1})_{jj}<1\}$), the corrected outputs (6.13) with the auxiliary symmetric $J$, the Householder reconstruction $G=\sqrt h\,H_{\rm rec}(z,\eta_1,\dots,\eta_{m_f-1})^\top$ (6.9)–(6.10), the updates (6.14), the initial magnetization $\sqrt\Delta\,\mathbf 1$, the vector $f=\widehat M_K-\sqrt\Delta\mathbf 1$ (6.15), the coordinate paths and increments, the final proof-only query $q_d$ and the matrix $Z$ of corrected outputs with it appended (§6.5), clipping and sequential rounding (Algorithm 1, lines 22–27). The randomness: $A\sim$ GOE$(N)$, $J$ with law (5.7) (variances $1/N$, $2/N$), i.i.d. standard Gaussian side variables, and their product law.
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), (5.7) p. 16; §6.3–§6.5 pp. 18–20; Algorithm 1 p. 66

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Scalar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
# The grouped query construction of GEG-IAMP as a mathematical map

Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1 (SHA-256 ea6508af…5658e):
(5.7) p. 16 (`J`), §6.3 (6.9)–(6.11) p. 18 (Gaussian reconstruction), §6.4 (6.12)–(6.15)
pp. 18–19 (queries, corrected outputs, updates, output), §6.5 p. 20 (the final query used only
in the proof), Algorithm 1 lines 22–27 p. 66 (clipping and sequential rounding).

This module writes the construction as a function of its randomness — the input `A`, the
auxiliary symmetric matrix `J`, the side variables `η` — for **fixed deterministic
normalization factors** `ω_k` (the magnetization increment is `a(t_j, Y_{j,i}) G_{j,i}/ω_j`,
§8.1 p. 39; the executed algorithm has `ω ≡ 1`). It is used by the matrix milestones
(Propositions 8.2, 8.4, Lemmas 8.13, 8.15); the costed program of Algorithm 1 is in
`Def_GEGIAMP_Relative_Algorithm`.

**Conventions.** Queries and groups are **0-based**: the paper's query/group `s ∈ {1, …, B}` is
Lean's `s − 1`, and the final proof-only query `q_d`, `d = B + 1`, is Lean's index `B`. `J` is
read as a function `ℕ → ℕ → ℝ` of (0-based) query indices; the side variable `η_{s,i,j}`
(`1 ≤ j ≤ m_f − 1`) is `η s i (j − 1)`.
-/

namespace GEGIAMP.Relative

variable {N : ℕ}

/-- Euclidean inner product. -/
def dot (x y : Fin N → ℝ) : ℝ := ∑ i, x i * y i

/-- The residual `F − ∑_{q ∈ qs} (qᵀF/N) q` of (6.12) (projection off the span of earlier
queries, which are orthogonal with norm `√N`). -/
noncomputable def resid (qs : List (Fin N → ℝ)) (F : Fin N → ℝ) : Fin N → ℝ :=
  fun i => F i - (qs.map fun q => dot q F / (N : ℝ) * q i).sum

/-- `λ_i = (P_{s−1})_{ii} = ∑_{q ∈ qs} q_i²/N`, the diagonal of the projection (App. A, p. 65). -/
noncomputable def lamDiag (qs : List (Fin N → ℝ)) (i : Fin N) : ℝ :=
  (qs.map fun q => q i ^ 2 / (N : ℝ)).sum

/-- The standard coordinate vector `e_i`. -/
def evec (i : Fin N) : Fin N → ℝ := fun j => if j = i then 1 else 0

open Classical in
/-- The next query of (6.12) and the rule after it (p. 19): if the residual `r` of `F` is
nonzero, `q = √N r/‖r‖`; otherwise take the smallest `i` with `(P_{s−1})_{ii} < 1`, project
`e_i` off the earlier queries and normalize. (If no such `i` exists — impossible while
`s ≤ N` — the zero vector is returned.) -/
noncomputable def nextQuery (qs : List (Fin N → ℝ)) (F : Fin N → ℝ) : Fin N → ℝ :=
  let r := resid qs F
  if vnorm r ≠ 0 then fun i => Real.sqrt N * r i / vnorm r
  else if h : ∃ i : Fin N, lamDiag qs i < 1 then
    let istar : Fin N := (Finset.univ.filter fun i => lamDiag qs i < 1).min'
      (h.elim fun i hi => ⟨i, by simp [hi]⟩)
    let r' := resid qs (evec istar)
    fun i => Real.sqrt N * r' i / vnorm r'
  else fun _ => 0

/-- The matrix–vector product `A x`. -/
def mulVec (A : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ := fun i => ∑ j, A i j * x j

/-- The corrected query output (6.13) for the query `q` with 0-based index `s = qs.length`:
`z = v + ½(J_ss − qᵀv/N) q + ∑_{r<s} (J_rs − q_rᵀ v/N) q_r`, `v = A q`. -/
noncomputable def corrected (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ)
    (qs : List (Fin N → ℝ)) (q : Fin N → ℝ) : Fin N → ℝ :=
  let v := mulVec A q
  let s := qs.length
  fun i => v i + (1 / 2 : ℝ) * (J s s - dot q v / (N : ℝ)) * q i +
    ((List.range s).map fun r =>
      (J r s - dot (qs.getD r 0) v / (N : ℝ)) * (qs.getD r 0) i).sum

/-- The Householder reconstruction (6.9)–(6.10): for `x ∈ ℝ^{m_f}`, `H_rec x` with
`v = m_f^{-1/2} 1`, `u = e_1 − v`, `H_rec = I − 2uuᵀ/‖u‖²` if `m_f > 1` and `H_rec = I` if
`m_f = 1`. Coordinates are 0-based (`e_1` is coordinate `0`). -/
noncomputable def householder (mf : ℕ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  if mf = 1 then x j
  else
    let u : ℕ → ℝ := fun k => (if k = 0 then 1 else 0) - 1 / Real.sqrt mf
    let uu := ∑ k ∈ Finset.range mf, u k ^ 2
    let ux := ∑ k ∈ Finset.range mf, u k * x k
    x j - 2 * ux / uu * u j

/-- The reconstructed increments of one coordinate in one group (6.10):
`(G_j)_{j ∈ I_s} = √h H_rec (z_s, η_{s,1}, …, η_{s,m_f−1})ᵀ`, indexed by the local step
`0 ≤ j' < m_f`. -/
noncomputable def recon (P : Params) (z : ℝ) (η : ℕ → ℝ) (j' : ℕ) : ℝ :=
  Real.sqrt P.h * householder P.mf (fun k => if k = 0 then z else η (k - 1)) j'

/-- Inside group `s` (0-based), the state `(Y, M̂)` of one coordinate after `j'` local steps of
(6.14) with increments `G` (local index), drift coefficients `Γc` and normalization factors `ω`:
`Y ← Y + Γc_j m(t_j, Y) + G_j`, `M̂ ← M̂ + a(t_j, Y) G_j/ω_j`, `j = s m_f + j'`, both updates
using the previous `Y`. -/
noncomputable def inner (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ) (s : ℕ)
    (y0 m0 : ℝ) (G : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (y0, m0)
  | j' + 1 =>
    let st := inner mo ao P Γc ω s y0 m0 G j'
    let j := s * P.mf + j'
    (st.1 + Γc j * mo (P.t j) st.1 + G j', st.2 + ao (P.t j) st.1 * G j' / ω j)

/-- The state of the construction after `s` executed groups. -/
structure CState (N : ℕ) where
  /-- The state vector `Y`. -/
  Y : Fin N → ℝ
  /-- The magnetization vector `M̂`. -/
  M : Fin N → ℝ
  /-- The queries `q_1, …, q_s` (0-based list). -/
  qs : List (Fin N → ℝ)
  /-- The corrected query outputs `z_1, …, z_s`. -/
  zs : List (Fin N → ℝ)
  /-- The reconstructed increments of each group: `Gs[s] i j'` is `G_{s m_f + j', i}`. -/
  Gs : List (Fin N → ℕ → ℝ)

/-- The construction after `s` groups (§6.4): `Y_0 = 0`, `M̂_0 = √Δ 1`; at the start of each
group propose `F = M̂`, form the query by (6.12), its corrected output by (6.13) (one product
with `A`), reconstruct the increments of every coordinate by (6.10) and run the updates (6.14).
-/
noncomputable def cstate (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) : ℕ → CState N
  | 0 => { Y := fun _ => 0, M := fun _ => Real.sqrt P.Δ, qs := [], zs := [], Gs := [] }
  | s + 1 =>
    let st := cstate mo ao P Γc ω A J η s
    let q := nextQuery st.qs st.M
    let z := corrected A J st.qs q
    let G : Fin N → ℕ → ℝ := fun i => recon P (z i) (η s i)
    let fin : Fin N → ℝ × ℝ := fun i => inner mo ao P Γc ω s (st.Y i) (st.M i) (G i) P.mf
    { Y := fun i => (fin i).1, M := fun i => (fin i).2, qs := st.qs ++ [q], zs := st.zs ++ [z],
      Gs := st.Gs ++ [G] }

/-- The final state after the `B` executed groups. -/
noncomputable def cfinal (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) : CState N :=
  cstate mo ao P Γc ω A J η P.B

/-- The vector before clipping, `f = M̂_K − √Δ 1` (6.15). -/
noncomputable def fvec (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) : Fin N → ℝ :=
  fun i => (cfinal mo ao P Γc ω A J η).M i - Real.sqrt P.Δ

/-- The path `(Y_{j,i}, M̂_{j,i} − √Δ)` of coordinate `i` at time-grid index `0 ≤ j ≤ K`
(for `m_f ≥ 1`): group `s = ⌊j/m_f⌋`, local step `j mod m_f`; the increments of group `s` are
those formed when group `s` is executed. -/
noncomputable def pathAt (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) (i : Fin N) (j : ℕ) :
    ℝ × ℝ :=
  let s := j / P.mf
  let st := cstate mo ao P Γc ω A J η s
  let G : ℕ → ℝ := ((cstate mo ao P Γc ω A J η (s + 1)).Gs.getD s (fun _ _ => 0)) i
  let y := inner mo ao P Γc ω s (st.Y i) (st.M i) G (j % P.mf)
  (y.1, y.2 - Real.sqrt P.Δ)

/-- The reconstructed increment `G_{j,i}` (`0 ≤ j < K`). -/
noncomputable def incr (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) (i : Fin N) (j : ℕ) : ℝ :=
  ((cfinal mo ao P Γc ω A J η).Gs.getD (j / P.mf) (fun _ _ => 0)) i (j % P.mf)

/-- The final query `q_d` used only in the proof (§6.5, p. 20): formed from `F_d = M̂_K` by the
rule (6.12) against the `B` executed queries. -/
noncomputable def finalQuery (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) : Fin N → ℝ :=
  let st := cfinal mo ao P Γc ω A J η
  nextQuery st.qs st.M

/-- The corrected query outputs of the **construction with the final query appended**:
`Z = [z_1 | ⋯ | z_d]`, column `s` (0-based); column `B` is `z_d`, formed from `q_d` by (6.13)
with the entries `J_{r,B}` of the last row/column. -/
noncomputable def Zext (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) (i : Fin N) (s : ℕ) : ℝ :=
  let st := cfinal mo ao P Γc ω A J η
  if s < P.B then (st.zs.getD s 0) i
  else corrected A J st.qs (finalQuery mo ao P Γc ω A J η) i

/-! ## Sequential rounding (Algorithm 1, lines 22–27, p. 66) -/

/-- Sequential rounding of `v`: `ℓ = Av − diag(A)v`; for `i = 1, …, N` in order, `s_i = +1` if
`ℓ_i ≥ 0` and `−1` otherwise, `δ_i = s_i − v_i`, `v_i ← s_i`, `ℓ ← ℓ + δ_i Ã_{:,i}` with
`Ã = A − diag(A)`. `roundAux A v k` is `(v, ℓ)` after the first `k` coordinates. -/
noncomputable def roundAux (A : Fin N → Fin N → ℝ) (v : Fin N → ℝ) :
    ℕ → (Fin N → ℝ) × (Fin N → ℝ)
  | 0 => (v, fun k => ∑ j, A k j * v j - A k k * v k)
  | n + 1 =>
    let st := roundAux A v n
    if hn : n < N then
      let i : Fin N := ⟨n, hn⟩
      let si : ℝ := if 0 ≤ st.2 i then 1 else -1
      let δ := si - st.1 i
      (Function.update st.1 i si, fun k => st.2 k + δ * (if k = i then 0 else A k i))
    else st

/-- The rounded spin configuration `σ` (Algorithm 1, line 28). -/
noncomputable def seqRound (A : Fin N → Fin N → ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  (roundAux A v N).1

/-- The output of the construction: `σ = seqRound(A, clip(f, [−1,1]^N))`. -/
noncomputable def sigmaOut (mo ao : ℝ → ℝ → ℝ) (P : Params) (Γc ω : ℕ → ℝ)
    (A : Fin N → Fin N → ℝ) (J : ℕ → ℕ → ℝ) (η : ℕ → Fin N → ℕ → ℝ) : Fin N → ℝ :=
  seqRound A (clipVec (fvec mo ao P Γc ω A J η))

/-! ## The randomness: `A`, `J` and the side variables -/

/-- The law (5.7) of a `d × d` symmetric `J` with independent entries on and above the
diagonal, `J_st ∼ N(0, 1/N)` (`s < t`), `J_tt ∼ N(0, 2/N)` — variances `1/N`, `2/N`, not
`1/d`, `2/d`. -/
noncomputable def jLaw (N d : ℕ) : Measure (Fin d → Fin d → ℝ) :=
  (Measure.pi fun p : RandMatDisc.SymIdx d =>
    gaussianReal 0 (if p.1.1 = p.1.2 then 2 / (N : ℝ≥0) else 1 / (N : ℝ≥0))).map
      RandMatDisc.symOfUpper

/-- Index set of the side variables: group `s < B`, coordinate `i`, component `j < m_f − 1`. -/
abbrev SideIdx (B N mf : ℕ) : Type := Fin B × Fin N × Fin (mf - 1)

/-- The side variables: independent standard Gaussians. -/
noncomputable def sideLaw (B N mf : ℕ) : Measure (SideIdx B N mf → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- `J` as a function of 0-based query indices (zero outside `d × d`). -/
def Jfun {d : ℕ} (J : Fin d → Fin d → ℝ) : ℕ → ℕ → ℝ :=
  fun r s => if h : r < d ∧ s < d then J ⟨r, h.1⟩ ⟨s, h.2⟩ else 0

/-- The leading `B × B` block of `J` only (the entries the executed algorithm draws). -/
def Jlead {d : ℕ} (B : ℕ) (J : Fin d → Fin d → ℝ) : ℕ → ℕ → ℝ :=
  fun r s => if r < B ∧ s < B then Jfun J r s else 0

/-- The side variables as a function `η s i j` (zero outside the index set). -/
def sideFun {B N mf : ℕ} (η : SideIdx B N mf → ℝ) : ℕ → Fin N → ℕ → ℝ :=
  fun s i j => if h : s < B ∧ j < mf - 1 then η (⟨s, h.1⟩, i, ⟨j, h.2⟩) else 0

/-- The sample space of the matrix analysis: `A`, the full `d × d` matrix `J` (its last
row/column is used only by the proof-only final query) and the side variables. -/
abbrev MatSpace (N : ℕ) (P : Params) : Type :=
  (Fin N → Fin N → ℝ) × ((Fin P.d → Fin P.d → ℝ) × (SideIdx P.B N P.mf → ℝ))

/-- The joint law `GOE(N) ⊗ law(J) ⊗ side variables`. -/
noncomputable def matLaw (N : ℕ) (P : Params) : Measure (MatSpace N P) :=
  (RandMatDisc.goe N).prod ((jLaw N P.d).prod (sideLaw P.B N P.mf))

end GEGIAMP.Relative


