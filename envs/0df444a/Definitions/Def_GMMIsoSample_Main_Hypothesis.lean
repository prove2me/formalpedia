-- Prove2me | Definitions.Def_GMMIsoSample_Main_Hypothesis
-- name    : GMMIsoSample_Main_Hypothesis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:18.88221+00:00
-- url     : https://prove2.me/theorems/2d4ad04f-4c2a-490e-8526-cc31587cbe83
-- title:
--   ConstructHypothesisDistribution2 and ConstructHypothesisDistributionk (Figures 3 and 4)
-- statement:
--   Both algorithms receive the **true clustering** $S'_1\sqcup\dots\sqcup S'_k$ of $N$ i.i.d. points (a labelled sample) and a uniformly random permutation $\pi$ of the indices, which supplies their random subsets and pairings: `compList z π i` lists the points of $S'_i$ in the order of $\pi$.
--
--   **ConstructHypothesisDistribution2** (Figure 3): $n_i=|S'_i|$, $\hat w_i=n_i/N$, $s=\lfloor\min\{n_1,n_2\}/4\rfloor$ (failure if $s=0$); disjoint size-$s$ subsets $M_i^{(1)},M_i^{(2)}$ with rest $R_i$; $D_a=\bar X_1^{(a)}-\bar X_2^{(a)}$, $\hat Q=\langle D_1,D_2\rangle$, $\hat\Delta=\sqrt{\max\{\hat Q,0\}}$; $r_i=\lfloor|R_i|/2\rfloor$ and
--   $$\hat\sigma_i^2=\frac1{2dr_i}\sum_{j=1}^{r_i}\|U_{i,j}-U'_{i,j}\|^2;$$
--   output $\hat w_1N(0,\hat\sigma_1^2I_d)+\hat w_2N(\hat\Delta e_1,\hat\sigma_2^2I_d)$.
--
--   **ConstructHypothesisDistributionk** (Figure 4): $\hat w_i=n_i/N$, $n=\lfloor\tfrac12\min_in_i\rfloor$ (failure if $n<2$), disjoint size-$n$ subsets $U_i,V_i$; $m=\lfloor n/2\rfloor$, $\hat\sigma_i^2=\frac1{2dm}\sum_{j\le m}\|U_{i,2j-1}-U_{i,2j}\|^2$; $\bar\mu_i$ the mean of $V_i$, $\hat q_{ij}=\|\bar\mu_i-\bar\mu_j\|^2-\frac dn(\hat\sigma_i^2+\hat\sigma_j^2)$, $\hat q_{ii}=0$; $a$ an index minimizing $\hat\sigma_i$; $S_{ij}=(\hat q_{ai}+\hat q_{aj}-\hat q_{ij})/(2\hat\sigma_i\hat\sigma_j)$ on $[k]\setminus\{a\}$; $\hat G=S_+$ (negative eigenvalues set to $0$); vectors $\hat x_i$ with $\langle\hat x_i,\hat x_j\rangle=\hat G_{ij}$; $\hat\mu_a=0$, $\hat\mu_i=\hat\sigma_i\hat x_i$; output $\sum_i\hat w_iN(\hat\mu_i,\hat\sigma_i^2I_d)$. `chdkOutputs` is the set of outputs over all admissible choices of $a$, of the diagonalization and of $\hat X$. `HypSucceeds ε D o` means $o$ is a valid mixture $\hat D$ with $\inf_\tau d_{TV}(\hat D,\tau(D))\le\varepsilon$.
--
--   **Formalization Note.** A size-$s$ uniformly random subset is a run of $s$ consecutive entries of the $\pi$-ordered list, and a random pairing pairs consecutive entries; for uniform $\pi$ these have the laws the figures prescribe. $e_1$ is the first standard basis vector, $\hat\sigma_i=\sqrt{\hat\sigma_i^2}$.
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 21, Figure 3; p. 27, Figure 4

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-!
# Hypothesis construction from a correctly clustered sample (Figures 3 and 4)

Chen, De, Lee, Servedio, *Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to
Isometry*, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…):
ConstructHypothesisDistribution2 (Figure 3), p. 21; ConstructHypothesisDistributionk (Figure 4),
p. 27.

Conventions.
* The input is a labelled sample `x : Fin N → Fin k × ℝ^d` (true component label, point); the
  true clustering `S'_i` is the set of points with label `i`.
* The algorithms' random subsets and random pairings are read off one uniformly random
  permutation `π` of the sample indices: `compList z π i` lists the indices of `S'_i` in the
  order of `π`; a size-`s` uniformly random subset is a run of `s` consecutive entries of that
  list, and a random pairing pairs consecutive entries. For uniform `π` this gives uniformly
  random disjoint subsets and a uniformly random pairing, as the figures prescribe.
* The free choices of Figure 4 (the anchor `a` among the minimizers of `σ̂_i`, the orthogonal
  diagonalization behind `S₊`, and the factor `X̂` with `X̂ᵀX̂ = Ĝ`) are left open:
  `chdkOutputs` is the set of all outputs over all admissible choices.
* `e₁` is the first standard basis vector of `ℝ^d` (`0` if `d = 0`).
-/

/-- The indices of component `i` in the order of the permutation `π`. -/
def compList {N k : ℕ} (z : Fin N → Fin k) (π : Equiv.Perm (Fin N)) (i : Fin k) :
    List (Fin N) :=
  ((List.finRange N).map π).filter (fun t => z t = i)

/-- Empirical mean of the points with indices in `l`. -/
noncomputable def listMean {d N : ℕ} (X : Fin N → E d) (l : List (Fin N)) : E d :=
  ((l.length : ℝ))⁻¹ • (l.map X).sum

/-- `(1/(2dr)) Σ_{j<r} ‖U_{2j} − U_{2j+1}‖²`, the paired-difference radius estimate on the first
`2r` entries of `l` (consecutive pairs). -/
noncomputable def pairedRadiusSq {d N : ℕ} (X : Fin N → E d) (l : List (Fin N)) (r : ℕ) : ℝ :=
  (1 / (2 * (d : ℝ) * r)) *
    ∑ j ∈ Finset.range r, ‖(l.map X).getD (2 * j) 0 - (l.map X).getD (2 * j + 1) 0‖ ^ 2

/-- `e₁ ∈ ℝ^d`. -/
noncomputable def firstBasis (d : ℕ) : E d :=
  if h : 0 < d then EuclideanSpace.single ⟨0, h⟩ 1 else 0

/-- ConstructHypothesisDistribution2(S'₁, S'₂) (Figure 3) on the labelled sample `x` with random
permutation `π`. Step 1: `n_i = |S'_i|`, `ŵ_i = n_i/N`, `s = ⌊min{n₁,n₂}/4⌋` (failure if `0`),
disjoint subsets `M_i^(1), M_i^(2)` of size `s`, rest `R_i`. Step 2: `D_a = X̄₁^(a) − X̄₂^(a)`,
`Q̂ = ⟨D₁, D₂⟩`, `Δ̂ = √max{Q̂, 0}`. Step 3: `r_i = ⌊|R_i|/2⌋`,
`σ̂_i² = (1/(2dr_i)) Σ_j ‖U_{i,j} − U'_{i,j}‖²`. Step 4: output
`ŵ₁ N(0, σ̂₁² I_d) + ŵ₂ N(Δ̂ e₁, σ̂₂² I_d)` (as the parameter tuple, with `σ̂_i = √(σ̂_i²)`). -/
noncomputable def chd2 {d N : ℕ} (x : Fin N → Fin 2 × E d) (π : Equiv.Perm (Fin N)) :
    Option (Params d 2) :=
  let z : Fin N → Fin 2 := fun t => (x t).1
  let X : Fin N → E d := fun t => (x t).2
  let S : Fin 2 → List (Fin N) := compList z π
  let n : Fin 2 → ℕ := fun i => (S i).length
  let s : ℕ := min (n 0) (n 1) / 4
  if s = 0 then none
  else
    let M₁ : Fin 2 → List (Fin N) := fun i => (S i).take s
    let M₂ : Fin 2 → List (Fin N) := fun i => ((S i).drop s).take s
    let R : Fin 2 → List (Fin N) := fun i => (S i).drop (2 * s)
    let D₁ : E d := listMean X (M₁ 0) - listMean X (M₁ 1)
    let D₂ : E d := listMean X (M₂ 0) - listMean X (M₂ 1)
    let Δ : ℝ := Real.sqrt (max (inner ℝ D₁ D₂) 0)
    let σ2 : Fin 2 → ℝ := fun i => pairedRadiusSq X (R i) ((R i).length / 2)
    some ![((n 0 : ℝ) / N, Real.sqrt (σ2 0), 0),
           ((n 1 : ℝ) / N, Real.sqrt (σ2 1), Δ • firstBasis d)]

/-- `G = S₊`: `G` is obtained from the symmetric matrix `S` by replacing its negative eigenvalues
by `0` (`S = O diag(λ) Oᵀ` with `O` orthogonal, `G = O diag(max(λ, 0)) Oᵀ`). -/
def IsPosPart {ι : Type*} [Fintype ι] [DecidableEq ι] (S G : Matrix ι ι ℝ) : Prop :=
  ∃ O ∈ Matrix.orthogonalGroup ι ℝ, ∃ lam : ι → ℝ,
    S = O * Matrix.diagonal lam * O.transpose ∧
    G = O * Matrix.diagonal (fun i => max (lam i) 0) * O.transpose

/-- ConstructHypothesisDistributionk(S'₁, …, S'_k) (Figure 4) on the labelled sample `x` with
random permutation `π`: every output over all admissible free choices. Step 1: `n_i = |S'_i|`,
`ŵ_i = n_i/N`, `n = ⌊½ min_i n_i⌋` (failure if `n < 2`), disjoint size-`n` subsets `U_i, V_i`.
Step 2: `m = ⌊n/2⌋`, `σ̂_i² = (1/(2dm)) Σ_{j≤m} ‖U_{i,2j−1} − U_{i,2j}‖²`. Step 3:
`μ̄_i` = mean of `V_i`, `q̂_ij = ‖μ̄_i − μ̄_j‖² − (d/n)(σ̂_i² + σ̂_j²)`, `q̂_ii = 0`. Step 4: `a`
minimizes `σ̂_i`; `S_ij = (q̂_ai + q̂_aj − q̂_ij)/(2σ̂_iσ̂_j)` on `[k]∖{a}`; `Ĝ = S₊`; columns
`x̂_i` with `⟨x̂_i, x̂_j⟩ = Ĝ_ij`. Step 5: `μ̂_a = 0`, `μ̂_i = σ̂_i x̂_i`; output
`Σ_i ŵ_i N(μ̂_i, σ̂_i² I_d)`. Failure also if no admissible choice exists. -/
noncomputable def chdkOutputs {d N k : ℕ} (x : Fin N → Fin k × E d) (π : Equiv.Perm (Fin N)) :
    Set (Option (Params d k)) :=
  open Classical in
  let z : Fin N → Fin k := fun t => (x t).1
  let X : Fin N → E d := fun t => (x t).2
  let S : Fin k → List (Fin N) := compList z π
  let nc : Fin k → ℕ := fun i => (S i).length
  let n : ℕ := sInf (Set.range nc) / 2
  let U : Fin k → List (Fin N) := fun i => (S i).take n
  let V : Fin k → List (Fin N) := fun i => ((S i).drop n).take n
  let σ2 : Fin k → ℝ := fun i => pairedRadiusSq X (U i) (n / 2)
  let σh : Fin k → ℝ := fun i => Real.sqrt (σ2 i)
  let μb : Fin k → E d := fun i => listMean X (V i)
  let qh : Fin k → Fin k → ℝ := fun i j =>
    if i = j then 0 else ‖μb i - μb j‖ ^ 2 - ((d : ℝ) / n) * (σ2 i + σ2 j)
  let Smat : (a : Fin k) → Matrix {i // i ≠ a} {i // i ≠ a} ℝ := fun a i j =>
    (qh a i + qh a j - qh i j) / (2 * σh i * σh j)
  let adm : (a : Fin k) → Matrix {i // i ≠ a} {i // i ≠ a} ℝ → ({i // i ≠ a} → E d) → Prop :=
    fun a G xh => (∀ i, σh a ≤ σh i) ∧ IsPosPart (Smat a) G ∧
      ∀ i j, inner ℝ (xh i) (xh j) = G i j
  let build : (a : Fin k) → ({i // i ≠ a} → E d) → Params d k := fun a xh i =>
    ((nc i : ℝ) / N, σh i, if h : i = a then 0 else σh i • xh ⟨i, h⟩)
  if n < 2 then {none}
  else if ∃ a G xh, adm a G xh then {o | ∃ a G xh, adm a G xh ∧ o = some (build a xh)}
  else {none}

/-- The output `o` of a hypothesis-construction algorithm succeeds for the target law `D`: it is a
valid spherical mixture `D̂` with `inf_{τ ∈ Iso(ℝ^d)} d_TV(D̂, τ(D)) ≤ ε`. -/
def HypSucceeds {d k : ℕ} (ε : ℝ) (D : Measure (E d)) (o : Option (Params d k)) : Prop :=
  ∃ h, o = some h ∧ IsValidParams h ∧
    (⨅ τ : E d ≃ᵢ E d, PolySampIso.tvDist (mix h) (D.map τ)) ≤ ε

end GMMIsoSample.Main


