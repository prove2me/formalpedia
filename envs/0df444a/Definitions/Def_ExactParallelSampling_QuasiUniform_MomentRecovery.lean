-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_MomentRecovery
-- name    : ExactParallelSampling_QuasiUniform_MomentRecovery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:11.442047+00:00
-- url     : https://prove2.me/theorems/e2f100bf-17c1-4590-8449-0287a0835b0c
-- title:
--   The adaptive moment-recovery procedure of Lemma 5.5
-- statement:
--   Steps 1–5 of Lemma 5.5 (pp. 26–27), as a function of $B$, of $r=s_x$ and of the support-size answers $s(Z)$, $Z\subseteq B$. The procedure is never given $h=|H|$.
--
--   - **Answers.** `momF r ss Z` $=F(Z)=1/s(Z)-1/r$.
--   - **Gram matrices.** `gram B F C` $=G_C=(F(B\setminus(S\cup S')))_{S,S'\in C}$. Querying it means asking the support-size queries `gramQueries B C` $=\{B\setminus(S\cup S')\}$ in one round.
--   - **Round families.** `candidates B T` $=T\cup\{S\cup S'\}\cup\{S\cup\{i\}\}$, so that $C_1=$ `candidates B {∅}` $=\{\emptyset\}\cup\{\{i\}:i\in B\}$.
--   - **Selection rule.** A rule `sel` is admissible (`IsMaxNonsingularSelection`) if, given $T'\subseteq C$ with nonsingular Gram matrix, it returns $T$ with $T'\subseteq T\subseteq C$ and nonsingular Gram matrix that is maximal (adding any further member of $C$ makes it singular), and its choice depends only on the entries of $G_C$. The greedy scans of the source, with $\emptyset$ first, are such rules.
--   - **Rounds.** `momT`: $T_0=\{\emptyset\}$ and $T_{j}=\mathrm{sel}(C_j,T_{j-1})$, with `momC j` $=C_j=$ `candidates`$(T_{j-1})$. `momStop` is the first round $j\ge2$ with $\operatorname{rank}G_{C_j}=|T_{j-1}|$ (or $0$ if none), and `momFinalT` $=T=T_{\text{stop}-1}$.
--   - **Recovery.** $K_i=(F(B\setminus(S_a\cup S_b\cup\{i\})))_{a,b}$ and $M_i=G_T^{-1}K_i$ (`momK`, `momM`). For a label set $A\subseteq B$ ($\lambda_i=0$ iff $i\in A$), `momLabelSpace A` $=\bigcap_{i\in A}\ker_\ell M_i\cap\bigcap_{i\in B\setminus A}\ker_\ell(M_i-I)$. This is the subspace the splitting of step 4 ends with for that label: the intersections commute, and a zero subspace stays zero.
--   - **Output.** `momOut` is the set of labels whose subspace is nonzero. `momLineVec A` is the vector $e$ of that line with $e(\emptyset)=1$. `momWeight A` is the diagonal entry of $E^{-\top}G_TE^{-1}$ at $A$, where $E$ has these vectors as rows.
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 5.5, steps 1–5, p. 26–27; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-! # The adaptive moment-recovery procedure of Lemma 5.5 (§5.2, pp. 26–27)

The procedure is given `B`, `r = s_x` and access to support-size queries `Z ↦ s(Z)` for `Z ⊆ B`;
it is **not** given `h = |H|`. From the answers it forms `F(Z) = 1/s(Z) − 1/r`. For a family `C`
of subsets of `B` the Gram matrix is `G_C = (F(B ∖ (S ∪ S')))_{S, S' ∈ C}`; querying `G_C` means
asking the support-size queries `B ∖ (S ∪ S')`, `S, S' ∈ C`, in one round.

1. Round 1: `C₁ = {∅} ∪ {{i} : i ∈ B}`; `T₁` a maximal subfamily of `C₁` with nonsingular Gram
   matrix, chosen greedily with `∅` first.
2. Round `j ≥ 2`: `C_j = T_{j−1} ∪ {S ∪ S'} ∪ {S ∪ {i}}`; stop with `T = T_{j−1}` if
   `rank G_{C_j} = |T_{j−1}|`, otherwise `T_j ⊇ T_{j−1}` a maximal subfamily of `C_j` with
   nonsingular Gram matrix.
3. At the stop: `G_T`, `K_i = (F(B ∖ (S_a ∪ S_b ∪ {i})))_{a,b}` (read off `G_{C_j}`) and
   `M_i = G_T⁻¹ K_i`.
4. Splitting by left kernels `ker_ℓ M_i` and `ker_ℓ (M_i − I)`, one coordinate `i ∈ B` at a time,
   dropping zero subspaces.
5. Output the label sets `A = {i : λ_i = 0}` of the surviving lines with the weights
   `diag(E^{−⊤} G_T E^{−1})`, `E` having as rows the line vectors `e` normalized by `e(∅) = 1`.

The choice of maximal nonsingular subfamilies is a parameter `sel`; the greedy scans of the source
are exactly the selections allowed by `IsMaxNonsingularSelection` (step 1 is `sel` applied with the
already selected family `{∅}`). -/

variable {E : Type*} [Fintype E]

/-- `F(Z) = 1/s(Z) − 1/r` from the support-size answers `ss`. -/
def momF (r : ℕ) (ss : Finset E → ℕ) (Z : Finset E) : ℝ :=
  1 / (ss Z : ℝ) - 1 / (r : ℝ)

/-- The Gram matrix `G_C[S, S'] = F(B ∖ (S ∪ S'))`. -/
def gram (B : Finset E) (Fv : Finset E → ℝ) (C : Finset (Finset E)) : Matrix ↥C ↥C ℝ :=
  fun S S' => Fv (B \ (S.1 ∪ S'.1))

/-- The support-size queries asked when querying `G_C`: the sets `B ∖ (S ∪ S')`, `S, S' ∈ C`. -/
def gramQueries (B : Finset E) (C : Finset (Finset E)) : Finset (Finset E) :=
  (C ×ˢ C).image (fun P => B \ (P.1 ∪ P.2))

/-- `T ∪ {S ∪ S' : S, S' ∈ T} ∪ {S ∪ {i} : S ∈ T, i ∈ B}`. With `T = {∅}` this is
`C₁ = {∅} ∪ {{i} : i ∈ B}`. -/
def candidates (B : Finset E) (T : Finset (Finset E)) : Finset (Finset E) :=
  T ∪ (T ×ˢ T).image (fun P => P.1 ∪ P.2) ∪ (T ×ˢ B).image (fun P => insert P.2 P.1)

/-- An admissible rule for choosing maximal nonsingular subfamilies: given the answers `Fv`, a
family `C` and an already chosen `T' ⊆ C` with nonsingular Gram matrix, it returns `T ⊇ T'`,
`T ⊆ C`, with nonsingular Gram matrix, to which no further member of `C` can be added keeping the
Gram matrix nonsingular; and its choice depends only on the entries of `G_C`. -/
def IsMaxNonsingularSelection (B : Finset E)
    (sel : (Finset E → ℝ) → Finset (Finset E) → Finset (Finset E) → Finset (Finset E)) : Prop :=
  (∀ Fv C T', T' ⊆ C → (gram B Fv T').det ≠ 0 →
      T' ⊆ sel Fv C T' ∧ sel Fv C T' ⊆ C ∧ (gram B Fv (sel Fv C T')).det ≠ 0 ∧
      ∀ S ∈ C, S ∉ sel Fv C T' → (gram B Fv (insert S (sel Fv C T'))).det = 0) ∧
  (∀ Fv Fv' C T', (∀ Z ∈ gramQueries B C, Fv Z = Fv' Z) → sel Fv C T' = sel Fv' C T')

variable (B : Finset E) (Fv : Finset E → ℝ)
  (sel : (Finset E → ℝ) → Finset (Finset E) → Finset (Finset E) → Finset (Finset E))

/-- `T_j`: `T₀ = {∅}` and `T_{j+1}` the selection in `C_{j+1}` extending `T_j`. -/
def momT : ℕ → Finset (Finset E)
  | 0 => {∅}
  | j + 1 => sel Fv (candidates B (momT j)) (momT j)

/-- `C_j = candidates(T_{j−1})`, the family whose Gram matrix is queried in round `j ≥ 1`. -/
def momC (j : ℕ) : Finset (Finset E) :=
  candidates B (momT B Fv sel (j - 1))

/-- The stopping round: the first `j ≥ 2` with `rank G_{C_j} = |T_{j−1}|` (`0` if there is none). -/
def momStop : ℕ :=
  if h : ∃ j, 2 ≤ j ∧ (gram B Fv (momC B Fv sel j)).rank = (momT B Fv sel (j - 1)).card then
    Nat.find h else 0

/-- `T`, the family at the stop. -/
def momFinalT : Finset (Finset E) :=
  momT B Fv sel (momStop B Fv sel - 1)

/-- `K_i[a, b] = F(B ∖ (S_a ∪ S_b ∪ {i}))` on `T`. -/
def momK (i : E) : Matrix ↥(momFinalT B Fv sel) ↥(momFinalT B Fv sel) ℝ :=
  fun a b => Fv (B \ (a.1 ∪ b.1 ∪ {i}))

/-- `M_i = G_T⁻¹ K_i`. -/
def momM (i : E) : Matrix ↥(momFinalT B Fv sel) ↥(momFinalT B Fv sel) ℝ :=
  (gram B Fv (momFinalT B Fv sel))⁻¹ * momK B Fv sel i

/-- The left kernel `ker_ℓ M = {e : e M = 0}`. -/
def leftKer {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker M.vecMulLinear

/-- After splitting along every `i ∈ B`, the subspace with label `λ`, where `λ_i = 0` iff `i ∈ A`:
`⋂_{i ∈ A} ker_ℓ M_i ∩ ⋂_{i ∈ B ∖ A} ker_ℓ (M_i − I)` (the successive intersections of step 4,
whose order does not matter; a pair is dropped as soon as its subspace is `0`). -/
def momLabelSpace (A : Finset E) : Submodule ℝ (↥(momFinalT B Fv sel) → ℝ) :=
  ⨅ (i : E) (_ : i ∈ B),
    (if i ∈ A then leftKer (momM B Fv sel i) else leftKer (momM B Fv sel i - 1))

/-- The output family: the sets `A ⊆ B` whose labelled subspace survived (is nonzero). -/
def momOut : Finset (Finset E) :=
  B.powerset.filter (fun A => momLabelSpace B Fv sel A ≠ ⊥)

/-- The vector `e` of the line with label `A`, normalized by `e(S₁) = e(∅) = 1`. -/
def momLineVec (A : Finset E) : ↥(momFinalT B Fv sel) → ℝ :=
  if h : ∃ e ∈ momLabelSpace B Fv sel A, ∃ h0 : (∅ : Finset E) ∈ momFinalT B Fv sel, e ⟨∅, h0⟩ = 1
  then Classical.choose h else 0

/-- The output weight of `A`: the diagonal entry of `E^{−⊤} G_T E^{−1}` at the row of `A`, where `E`
has the vectors `e` as rows (rows reindexed onto `T` by any bijection; the diagonal entry does
not depend on it). `0` if the number of lines differs from `|T|`. -/
def momWeight (A : Finset E) : ℝ :=
  if hc : Fintype.card ↥(momOut B Fv sel) = Fintype.card ↥(momFinalT B Fv sel) then
    if hA : A ∈ momOut B Fv sel then
      let eqv := Fintype.equivOfCardEq hc
      let Em : Matrix ↥(momFinalT B Fv sel) ↥(momFinalT B Fv sel) ℝ :=
        fun t S => momLineVec B Fv sel (eqv.symm t).1 S
      let W := Matrix.transpose Em⁻¹ * gram B Fv (momFinalT B Fv sel) * Em⁻¹
      W (eqv ⟨A, hA⟩) (eqv ⟨A, hA⟩)
    else 0
  else 0

end ExactParallelSampling.QuasiUniform


