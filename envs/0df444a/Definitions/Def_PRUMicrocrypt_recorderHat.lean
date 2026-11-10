-- Prove2me | Definitions.Def_PRUMicrocrypt_recorderHat
-- name    : PRUMicrocrypt_recorderHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:28:41.325977+00:00
-- url     : https://prove2.me/theorems/b383a63e-26ff-4894-bbdc-e23c03b29aec
-- title:
--   Relation registers, the recorders $V^L,V^R,V,W,\overline V,\overline W$ and the coherent recorder $\widehat V$ (3.2)–(3.18)
-- statement:
--   A **relation** is a finite multiset of edges $(x,y)\in\mathbb F_2^n\times\mathbb F_2^n$. A **record** $|L,R\rangle$ is a pair of relations of total size $|L|+|R|\le N$; by the normalization (3.2) these kets form an orthonormal basis of $\mathcal H_{LR}=\bigoplus_{\ell+r\le N}\mathcal R_\ell\otimes\mathcal R_r$. Write $\mathrm{Dom}(L\cup R)$ and $\mathrm{Im}(L\cup R)$ for the sets of first and second coordinates; $(L,R)$ is **bijective** when its union has distinct domains and distinct images. On the query register $\otimes\,\mathcal H_{LR}$, with every operator zero outside its stated domain:
--
--   1. On records of total size at most $N-1$,
--   $$V^L|x\rangle|L,R\rangle=\frac{1}{\sqrt{N-|\mathrm{Im}(L\cup R)|}}\sum_{y\notin\mathrm{Im}(L\cup R)}|y\rangle|L\cup\{(x,y)\},R\rangle,\qquad V^R|y\rangle|L,R\rangle=\frac{1}{\sqrt{N-|\mathrm{Dom}(L\cup R)|}}\sum_{x\notin\mathrm{Dom}(L\cup R)}|x\rangle|L,R\cup\{(x,y)\}\rangle,$$
--   and $V=V^L(I-V^RV^{R\dagger})+(I-V^LV^{L\dagger})V^{R\dagger}$.
--   2. On bijective records of size $s<N$, $W^L$ (for $x\notin\mathrm{Dom}$) and $W^R$ (for $y\notin\mathrm{Im}$) add the same edges with normalization $1/\sqrt{N-s}$, and $W=W^L+W^{R\dagger}$.
--   3. The barred recorders $\overline V^L,\overline V^R,\overline W^L,\overline W^R$ are the same maps with the roles of $L$ and $R$ exchanged (forward creation records a negative edge), and $\overline V,\overline W$ are formed as in item 1–2.
--   4. The common coherent recorder is $\widehat V=\sum_{a=0}^4P_a\otimes V_a$ with $(V_0,\dots,V_4)=(I,V,V^\dagger,\overline V^\dagger,\overline V)$, and the recorder trajectory is $|v_0\rangle=|\psi_0\rangle\otimes|\varnothing,\varnothing\rangle$, $|v_j\rangle=\widehat V(A_j\otimes I_{LR})|v_{j-1}\rangle$.
--
--   The module also defines $\mathrm{Tr}_{LR}$, the size projectors $\Pi_{\mathrm{size}=s}$, and the predicates partial isometry ($ZZ^\dagger Z=Z$), contraction and "increases record size by at most one".
--
--   These recorders are the path-recording machinery of Lemma 3.1 and Theorem H.2.
--
--   **Formalization Note** $\mathcal H_{LR}$ is encoded by its orthonormal basis of records (`Record n`), so operators are matrices indexed by (query label, record). The bar names the directly defined recorders; it is not entrywise conjugation.
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3.2, (3.2)–(3.18), pp.21–23

import Mathlib
import Definitions.Def_PRUMicrocrypt_QueryAlg

set_option autoImplicit false

namespace PRUMicrocrypt

open Matrix

/-- An edge `(x, y) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`, stored in forward input–output order (§3.2, p.21). -/
abbrev Edge (n : ℕ) := Idx n × Idx n

/-- **A record `|L, R⟩` of the two relation registers** (§3.2, (3.2), p.21): a pair of finite
multisets of edges `(L, R)` of total size `|L| + |R| ≤ N`, `N = 2ⁿ`. The kets `|L, R⟩` form an
orthonormal basis of `ℋ_LR = ⨁_{ℓ+r≤N} ℛ_ℓ ⊗ ℛ_r`, `ℛ_s = Sym^s(ℂᴺ ⊗ ℂᴺ)`.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3.2, (3.2), p.21.

**Formalization Note.** `ℋ_LR` is encoded by this orthonormal basis: an element is a pair of
sizes `(ℓ, r)` with `ℓ + r ≤ N` and two multisets of these sizes (`Sym`), so operators on
query ⊗ LR are matrices indexed by `Idx n × Record n`. The normalization (3.2) of the multiset
kets is what makes them orthonormal, so the encoding changes no operator. -/
abbrev Record (n : ℕ) :=
  {x : Σ p : Fin (2 ^ n + 1) × Fin (2 ^ n + 1), Sym (Edge n) p.1 × Sym (Edge n) p.2 //
    x.1.1.val + x.1.2.val ≤ 2 ^ n}

instance (n : ℕ) : DecidableEq (Record n) := Subtype.instDecidableEq

/-- The relation `L` (positive edges) of a record. -/
def Record.L {n : ℕ} (r : Record n) : Multiset (Edge n) := (r.1.2.1 : Multiset (Edge n))

/-- The relation `R` (negative edges) of a record. -/
def Record.R {n : ℕ} (r : Record n) : Multiset (Edge n) := (r.1.2.2 : Multiset (Edge n))

/-- The total size `|L| + |R|` of a record. -/
def Record.size {n : ℕ} (r : Record n) : ℕ := Multiset.card r.L + Multiset.card r.R

/-- `Dom(L ∪ R)`: the set of first coordinates of the edges of `L ∪ R`. -/
def Record.dom {n : ℕ} (r : Record n) : Finset (Idx n) := ((r.L + r.R).map Prod.fst).toFinset

/-- `Im(L ∪ R)`: the set of second coordinates of the edges of `L ∪ R`. -/
def Record.im {n : ℕ} (r : Record n) : Finset (Idx n) := ((r.L + r.R).map Prod.snd).toFinset

/-- `(L, R)` is bijective when its union has distinct domains and distinct images (§3.2, p.21). -/
def Record.IsBijective {n : ℕ} (r : Record n) : Prop :=
  ((r.L + r.R).map Prod.fst).Nodup ∧ ((r.L + r.R).map Prod.snd).Nodup

instance {n : ℕ} (r : Record n) : Decidable r.IsBijective := by
  unfold Record.IsBijective; infer_instance

/-- Operators on query register ⊗ LR, as matrices in the basis `|x⟩|L, R⟩`; the entry `Z p q` is
`⟨p| Z |q⟩`. -/
abbrev QLR (n : ℕ) := Idx n × Record n

/-- The normalization `1/√(N − c)` with `N = 2ⁿ`. -/
noncomputable def invSqrtGap (n c : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ n - c))⁻¹ : ℝ)

/-- `V^L` (3.3): on records of total size at most `N − 1`,
`V^L|x⟩|L, R⟩ = (N − |Im(L∪R)|)^{−1/2} ∑_{y ∉ Im(L∪R)} |y⟩|L ∪ {(x, y)}, R⟩`; zero elsewhere. -/
noncomputable def VL (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.size ≤ 2 ^ n - 1 ∧ p.1 ∉ q.2.im ∧ p.2.L = (q.1, p.1) ::ₘ q.2.L ∧ p.2.R = q.2.R
  then invSqrtGap n q.2.im.card else 0

/-- `V^R` (3.4): on records of total size at most `N − 1`,
`V^R|y⟩|L, R⟩ = (N − |Dom(L∪R)|)^{−1/2} ∑_{x ∉ Dom(L∪R)} |x⟩|L, R ∪ {(x, y)}⟩`; zero elsewhere. -/
noncomputable def VR (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.size ≤ 2 ^ n - 1 ∧ p.1 ∉ q.2.dom ∧ p.2.L = q.2.L ∧ p.2.R = (p.1, q.1) ::ₘ q.2.R
  then invSqrtGap n q.2.dom.card else 0

/-- The unrestricted recorder (3.5): `V = V^L(I − V^R V^{R†}) + (I − V^L V^{L†})V^{R†}`. -/
noncomputable def Vrec (n : ℕ) : Matrix (QLR n) (QLR n) ℂ :=
  VL n * (1 - VR n * (VR n)ᴴ) + (1 - VL n * (VL n)ᴴ) * (VR n)ᴴ

/-- `W^L` (3.6): on a bijective `(L, R)` of size `s < N` and `x ∉ Dom(L∪R)`,
`W^L|x⟩|L, R⟩ = (N − s)^{−1/2} ∑_{y ∉ Im(L∪R)} |y⟩|L ∪ {(x, y)}, R⟩`; zero elsewhere. -/
noncomputable def WL (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.IsBijective ∧ q.2.size < 2 ^ n ∧ q.1 ∉ q.2.dom ∧ p.1 ∉ q.2.im ∧
      p.2.L = (q.1, p.1) ::ₘ q.2.L ∧ p.2.R = q.2.R
  then invSqrtGap n q.2.size else 0

/-- `W^R` (3.7): on a bijective `(L, R)` of size `s < N` and `y ∉ Im(L∪R)`,
`W^R|y⟩|L, R⟩ = (N − s)^{−1/2} ∑_{x ∉ Dom(L∪R)} |x⟩|L, R ∪ {(x, y)}⟩`; zero elsewhere. -/
noncomputable def WR (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.IsBijective ∧ q.2.size < 2 ^ n ∧ q.1 ∉ q.2.im ∧ p.1 ∉ q.2.dom ∧
      p.2.L = q.2.L ∧ p.2.R = (p.1, q.1) ::ₘ q.2.R
  then invSqrtGap n q.2.size else 0

/-- The bijective partial recorder (3.8): `W = W^L + W^{R†}`. -/
noncomputable def Wrec (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := WL n + (WR n)ᴴ

/-- `V̄^L` (3.9): on records of total size at most `N − 1`,
`V̄^L|x⟩|L, R⟩ = (N − |Im(L∪R)|)^{−1/2} ∑_{y ∉ Im(L∪R)} |y⟩|L, R ∪ {(x, y)}⟩`; zero elsewhere. -/
noncomputable def VLbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.size ≤ 2 ^ n - 1 ∧ p.1 ∉ q.2.im ∧ p.2.L = q.2.L ∧ p.2.R = (q.1, p.1) ::ₘ q.2.R
  then invSqrtGap n q.2.im.card else 0

/-- `V̄^R` (3.10): on records of total size at most `N − 1`,
`V̄^R|y⟩|L, R⟩ = (N − |Dom(L∪R)|)^{−1/2} ∑_{x ∉ Dom(L∪R)} |x⟩|L ∪ {(x, y)}, R⟩`; zero elsewhere. -/
noncomputable def VRbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.size ≤ 2 ^ n - 1 ∧ p.1 ∉ q.2.dom ∧ p.2.L = (p.1, q.1) ::ₘ q.2.L ∧ p.2.R = q.2.R
  then invSqrtGap n q.2.dom.card else 0

/-- The barred recorder (3.13): `V̄ = V̄^L(I − V̄^R V̄^{R†}) + (I − V̄^L V̄^{L†})V̄^{R†}`. The bar
names this directly defined recorder; it is not entrywise conjugation. -/
noncomputable def Vbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ :=
  VLbar n * (1 - VRbar n * (VRbar n)ᴴ) + (1 - VLbar n * (VLbar n)ᴴ) * (VRbar n)ᴴ

/-- `W̄^L` (3.11): on a bijective `(L, R)` of size `s < N` and `x ∉ Dom(L∪R)`,
`W̄^L|x⟩|L, R⟩ = (N − s)^{−1/2} ∑_{y ∉ Im(L∪R)} |y⟩|L, R ∪ {(x, y)}⟩`; zero elsewhere. -/
noncomputable def WLbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.IsBijective ∧ q.2.size < 2 ^ n ∧ q.1 ∉ q.2.dom ∧ p.1 ∉ q.2.im ∧
      p.2.L = q.2.L ∧ p.2.R = (q.1, p.1) ::ₘ q.2.R
  then invSqrtGap n q.2.size else 0

/-- `W̄^R` (3.12): on a bijective `(L, R)` of size `s < N` and `y ∉ Im(L∪R)`,
`W̄^R|y⟩|L, R⟩ = (N − s)^{−1/2} ∑_{x ∉ Dom(L∪R)} |x⟩|L ∪ {(x, y)}, R⟩`; zero elsewhere. -/
noncomputable def WRbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := fun p q =>
  if q.2.IsBijective ∧ q.2.size < 2 ^ n ∧ q.1 ∉ q.2.im ∧ p.1 ∉ q.2.dom ∧
      p.2.L = (p.1, q.1) ::ₘ q.2.L ∧ p.2.R = q.2.R
  then invSqrtGap n q.2.size else 0

/-- The barred bijective recorder (3.14): `W̄ = W̄^L + W̄^{R†}`. -/
noncomputable def Wbar (n : ℕ) : Matrix (QLR n) (QLR n) ℂ := WLbar n + (WRbar n)ᴴ

/-- The projector `Π_{size = s}` onto records of total size exactly `s` (identity on the query). -/
noncomputable def sizeProj (n s : ℕ) : Matrix (QLR n) (QLR n) ℂ :=
  Matrix.diagonal fun p => if p.2.size = s then 1 else 0

/-- `Z` is a partial isometry: `Z Z† Z = Z`. -/
def IsPartialIsometry {ι : Type*} [Fintype ι] (Z : Matrix ι ι ℂ) : Prop := Z * Zᴴ * Z = Z

/-- `Z` is a contraction: `‖Z v‖ ≤ ‖v‖` for every vector `v`. -/
def IsContraction {ι : Type*} [Fintype ι] (Z : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, ∑ i, Complex.normSq ((Z *ᵥ v) i) ≤ ∑ i, Complex.normSq (v i)

/-- `Z` increases total record size by at most one: `⟨y, L', R'| Z |x, L, R⟩ ≠ 0` only if
`|L'| + |R'| ≤ |L| + |R| + 1`. -/
def IncreasesSizeAtMostOne {n : ℕ} (Z : Matrix (QLR n) (QLR n) ℂ) : Prop :=
  ∀ p q, Z p q ≠ 0 → p.2.size ≤ q.2.size + 1

/-- The recorder of each branch in the order `I, U, U†, Uᵀ, Ū` (3.17):
`(V₀, V₁, V₂, V₃, V₄) = (I, V, V†, V̄†, V̄)`. -/
noncomputable def recBranch (n : ℕ) : Fin 5 → Matrix (QLR n) (QLR n) ℂ
  | 0 => 1
  | 1 => Vrec n
  | 2 => (Vrec n)ᴴ
  | 3 => (Vbar n)ᴴ
  | 4 => Vbar n

/-- **The common coherent recorder** (3.17): `V̂ = ∑_{a=0}^{4} P_a ⊗ V_a`, acting on selector ⊗
query ⊗ LR and as the identity on the reference `W`.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3.2, (3.17), p.23.

**Formalization Note.** The global space is `(selector ⊗ query ⊗ W) ⊗ LR`, indexed by
`Acc n W × Record n`; `P_a = |a⟩⟨a|` on the selector `ℂ⁵`. -/
noncomputable def recorderHat (n : ℕ) (W : Type*) [DecidableEq W] :
    Matrix (Acc n W × Record n) (Acc n W × Record n) ℂ := fun p q =>
  if p.1.1 = q.1.1 ∧ p.1.2.2 = q.1.2.2 then recBranch n q.1.1 (p.1.2.1, p.2) (q.1.2.1, q.2)
  else 0

/-- `A ⊗ I_LR` for an operator `A` on the accessible registers. -/
def liftLR {n : ℕ} {W : Type*} (A : Matrix (Acc n W) (Acc n W) ℂ) :
    Matrix (Acc n W × Record n) (Acc n W × Record n) ℂ :=
  fun p q => if p.2 = q.2 then A p.1 q.1 else 0

/-- **The recorder trajectory** (3.18): `|v₀⟩ = |ψ₀⟩ ⊗ |∅, ∅⟩`, `|v_j⟩ = V̂ (A_j ⊗ I_LR)|v_{j−1}⟩`.
`alg.recorderState j` is `|v_j⟩` (possibly subnormalized).
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), (3.18), p.23. -/
noncomputable def QueryAlg.recorderState {n t : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) : ℕ → (Acc n W × Record n → ℂ) :=
  trajectory (fun j v => (recorderHat n W * liftLR (alg.op j)) *ᵥ v)
    (fun p => if p.2.L = 0 ∧ p.2.R = 0 then alg.ψ₀ p.1 else 0)

/-- The partial trace `Tr_LR |v⟩⟨v|` over the relation registers. -/
noncomputable def partialTraceLR {n : ℕ} {W : Type*} [Fintype W]
    (v : Acc n W × Record n → ℂ) : Matrix (Acc n W) (Acc n W) ℂ :=
  fun i j => ∑ r : Record n, v (i, r) * star (v (j, r))

end PRUMicrocrypt


