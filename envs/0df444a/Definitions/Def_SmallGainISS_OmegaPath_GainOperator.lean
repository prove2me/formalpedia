-- Prove2me | Definitions.Def_SmallGainISS_OmegaPath_GainOperator
-- name    : SmallGainISS_OmegaPath_GainOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:34.87201+00:00
-- url     : https://prove2.me/theorems/50c41525-8447-4735-95a6-1e5dc22f147a
-- title:
--   Orders on $\mathbb R^n_+$, classes $\mathcal K$, $\mathcal K_\infty$, MAFs, the gain operator $\Gamma_\mu$, (SGC), $\Omega$, $\Psi$, $\Psi_\infty$, irreducibility and cycles (§§2, 4, 8)
-- statement:
--   This file collects the objects of §2.1, §2.4, §4 and §8 of the paper that the existence theory for $\Omega$-paths is stated in.
--
--   1. **Orders on $\mathbb R^n_+$** (p. 5). For $v,w\in\mathbb R^n_+$, $v\le w$ means $v_i\le w_i$ for every $i$, and $v<w$ means $v_i<w_i$ for every $i$. A vector is *strictly positive*, $s>0$, if every component is positive.
--   2. **Comparison functions** (p. 5). $\mathcal K$ is the set of continuous, strictly increasing $\gamma:\mathbb R_+\to\mathbb R_+$ with $\gamma(0)=0$; $\mathcal K_\infty$ consists of the unbounded members of $\mathcal K$. Gains are taken from $\mathcal K\cup\{0\}$, $\mathcal K_\infty\cup\{0\}$ or $(\mathcal K\setminus\mathcal K_\infty)\cup\{0\}$.
--   3. **Monotone aggregation functions** (Definition 2.4, p. 7). A continuous $\mu:\mathbb R^n_+\to\mathbb R_+$ is a MAF if (M1) $\mu(s)>0$ whenever $s\ne0$; (M2) $x<y$ implies $\mu(x)<\mu(y)$; (M3) $\mu(x)\to\infty$ as $\|x\|\to\infty$.
--   4. **Gain operator** (2.9), without external input:
--   $$\Gamma_\mu(s)_i=\mu_i\big(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n)\big),\qquad s\in\mathbb R^n_+ .$$
--   The diagonal gains vanish, $\gamma_{ii}\equiv0$ (p. 8).
--   5. **Compatibility** (Remark 2.6, (2.10)). For each $i$ let $I_i=\{j:\gamma_{ij}\not\equiv0\}$. If $I_i\neq\emptyset$, then $\mu_i$ restricted to the coordinates in $I_i$ (the other coordinates set to $0$) satisfies (M2).
--   6. **Small gain condition** (SGC, p. 12): $T\not\ge\mathrm{id}$, meaning that for every $s\ne0$ it is not true that $s\le T(s)$; at least one component of $T(s)$ is strictly smaller than the corresponding component of $s$.
--   7. **Sets** (pp. 13, 23, 5): $\Omega(T)=\{s:T(s)<s\}$; the decay set $\Psi(T)=\{s:T(s)\le s\}$; $\Psi_\infty(T)=\bigcap_{k\ge0}T^k(\Psi(T))$ (images under iterates); $S_r=\{s\in\mathbb R^n_+:\sum_i s_i=r\}$, the sphere of the 1-norm.
--   8. **Diagonal operators**: $\mathrm{diag}(\rho)(s)_i=\rho(s_i)$, and $\rho>\mathrm{id}$ means $\rho(r)>r$ for all $r>0$. An operator $T$ is *strictly increasing* if $v<w$ implies $T(v)<T(w)$.
--   9. **Irreducibility** (p. 12). The adjacency matrix $A_\Gamma$ has $a_{ij}=0$ if $\gamma_{ij}\equiv0$ and $a_{ij}=1$ otherwise; $\Gamma$ is irreducible if for every pair $(i,j)$ there is $k\ge1$ with $(A_\Gamma^k)_{ij}>0$.
--   10. **Special operators.** $\mu=\max$ means $\mu_i(s)=\max_j s_j$ for every $i$. $\Gamma_\mu$ is *bounded* if $\Gamma_\mu(\mathbb R^n_+)$ is bounded. $\Gamma_\mu$ is *linear with spectral radius less than one* if $\Gamma_\mu(s)=Gs$ for a real matrix $G$ with nonnegative entries all of whose complex eigenvalues have modulus $<1$.
--   11. **Cycles** (§8.4, p. 27). A cycle is a sequence of nonzero entries $(\gamma_{i_1i_2},\gamma_{i_2i_3},\dots,\gamma_{i_Ki_1})$; it is *subordinated* if $i_1>\max\{i_2,\dots,i_K\}$ and a *contraction* if $\gamma_{i_1i_2}\circ\gamma_{i_2i_3}\circ\dots\circ\gamma_{i_Ki_1}(r)<r$ for all $r>0$.
--
--   These are the shared vocabulary of every statement in the mission.
--
--   **Formalization Note** $\mathbb R_+$ is `ℝ≥0` and $\mathbb R^n_+$ is `Fin n → ℝ≥0` (subsystems indexed from $0$). The strict order is the named predicate `SLt`, not Lean's `<` on functions (which means "$\le$ and $\ne$"). (M3) is stated with the cobounded filter of the sup metric, equivalent to $\|x\|\to\infty$ for any norm. In Remark 2.6 a row with $I_i=\emptyset$ imposes nothing, since (M2) can never hold for a constant function; (M4) subadditivity is not assumed, as on p. 7. A cycle of length $K$ is a map `Fin K → Fin n` ($K\ge1$), the successor of the last index being the first.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, pp. 5, 7-8, 12-13, 21-23, 27, §2.1, Definition 2.4, (2.8)-(2.10), Remark 2.6, (4.1), Definition 4.1, §8.4

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-! Dashkovskiy, Rüffer, Wirth, arXiv:0901.1842v2, §2.1 (p. 5), §2.4 (pp. 7–8), §4 (pp. 12–13),
§8 (pp. 21–27). The paper's subsystems `1, …, n` are `Fin n` (0-based). `ℝ₊` is `ℝ≥0`, and
`ℝⁿ₊` is `Fin n → ℝ≥0`. -/

variable {n : ℕ}

/-- `s > 0` in the paper's strict sense: every component is positive. -/
def SPos (s : Fin n → ℝ≥0) : Prop := ∀ i, 0 < s i

/-- `γ ∈ (𝒦 \ 𝒦∞) ∪ {0}`: zero, or of class `𝒦` and bounded. -/
def IsBoundedKOrZero (γ : ℝ≥0 → ℝ≥0) : Prop := (SmallGainISS.Lyapunov.IsK γ ∧ BddAbove (Set.range γ)) ∨ γ = 0

/-- The gain operator `Γ_μ : ℝⁿ₊ → ℝⁿ₊` for `μ ∈ MAFⁿₙ` (no external input, §§5, 8):
`Γ_μ(s)ᵢ = μᵢ(γᵢ₁(s₁), …, γᵢₙ(sₙ))`. -/
def gainOp (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0) (s : Fin n → ℝ≥0) :
    Fin n → ℝ≥0 :=
  fun i => μ i (fun j => Γ i j (s j))

/-- `Γ` has no zero rows: every row has a nonzero entry. -/
def NoZeroRows (Γ : SmallGainISS.Lyapunov.GainMatrix n) : Prop := ∀ i, ∃ j, Γ i j ≠ 0

/-- Remark 2.6 (general assumption, p. 8), (2.10): for each `i` with `Iᵢ = {j : γᵢⱼ ≠ 0}`
nonempty, the restriction of `μᵢ` to the coordinates `Iᵢ` (the others set to `0`) satisfies (M2):
if `xⱼ < yⱼ` for all `j ∈ Iᵢ`, then `μᵢ(x|Iᵢ) < μᵢ(y|Iᵢ)`. A row with `Iᵢ = ∅` imposes nothing
(the restriction to no coordinates is a constant, for which (M2) cannot hold). -/
def Compatible (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0) : Prop :=
  ∀ i, (∃ j, Γ i j ≠ 0) → ∀ x y : Fin n → ℝ≥0,
    (∀ j, Γ i j = 0 → x j = 0) → (∀ j, Γ i j = 0 → y j = 0) →
    (∀ j, Γ i j ≠ 0 → x j < y j) → μ i x < μ i y

/-- The small gain condition `T ≱ id` (SGC, p. 12): for all `s ≠ 0`, `T(s) ≱ s`, i.e.
it is not the case that `s ≤ T(s)` componentwise. -/
def SGC (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Prop := ∀ s, s ≠ 0 → ¬ (s ≤ T s)

/-- `T(v) < T(w)` whenever `v < w`, both in the strict componentwise sense
(Lemma 8.7(ii), Proposition 8.8, Theorem 8.11). -/
def StrictlyIncreasingOp (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Prop :=
  ∀ v w, SmallGainISS.Lyapunov.SLt v w → SmallGainISS.Lyapunov.SLt (T v) (T w)

/-- The decay set `Ψ(T) = {s ∈ ℝⁿ₊ : T(s) ≤ s}` (p. 23), non-strict. -/
def Psi (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Set (Fin n → ℝ≥0) := {s | T s ≤ s}

/-- `Ψ∞(T) = ⋂_{k ≥ 0} Tᵏ(Ψ)` (p. 23): the intersection of the images of `Ψ` under the iterates. -/
def PsiInf (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Set (Fin n → ℝ≥0) :=
  ⋂ k : ℕ, (T^[k]) '' Psi T

/-- The 1-norm `|s| = ∑ᵢ sᵢ` on `ℝⁿ₊` (p. 5). -/
def oneNorm (s : Fin n → ℝ≥0) : ℝ≥0 := ∑ i, s i

/-- `S_r`: the sphere of radius `r` of the 1-norm intersected with `ℝⁿ₊` (p. 5). -/
def sphereOne (n : ℕ) (r : ℝ≥0) : Set (Fin n → ℝ≥0) := {s | oneNorm s = r}

/-- The diagonal operator `diag(ρ)`: `diag(ρ)(s)ᵢ = ρ(sᵢ)` (§8; (4.1) is `diag(id + α)`). -/
def diagOp (ρ : ℝ≥0 → ℝ≥0) (s : Fin n → ℝ≥0) : Fin n → ℝ≥0 := fun i => ρ (s i)

/-- `ρ > id`: `ρ(r) > r` for all `r > 0`. -/
def GtId (ρ : ℝ≥0 → ℝ≥0) : Prop := ∀ r, 0 < r → r < ρ r

open Classical in
/-- The adjacency matrix `A_Γ` (p. 12): `aᵢⱼ = 0` if `γᵢⱼ ≡ 0`, and `1` otherwise. -/
noncomputable def adjMatrix (Γ : SmallGainISS.Lyapunov.GainMatrix n) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => if Γ i j = 0 then 0 else 1

/-- `Γ` is irreducible (p. 12): for every pair `(i, j)` there is `k ≥ 1` with `(A_Γᵏ)ᵢⱼ > 0`. -/
def IsIrreducible (Γ : SmallGainISS.Lyapunov.GainMatrix n) : Prop :=
  ∀ i j : Fin n, ∃ k : ℕ, 1 ≤ k ∧ 0 < (adjMatrix Γ ^ k) i j

/-- The aggregation `μ = max` (every `μᵢ` is the maximum of its arguments; `0` for `n = 0`). -/
def maxAgg : Fin n → (Fin n → ℝ≥0) → ℝ≥0 := fun _ s => Finset.univ.sup s

/-- `T` is bounded: its range `T(ℝⁿ₊)` is a bounded set (Theorem 5.2(iv), Proposition 8.4). -/
def IsBoundedOp (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Prop := Bornology.IsBounded (Set.range T)

/-- Theorem 5.2(i): `T` is linear, i.e. given by a real matrix `G` with nonnegative entries,
`T(s) = G s` on `ℝⁿ₊`, and the spectral radius of `G` is less than one (every complex
eigenvalue of `G` has modulus `< 1`). -/
def IsLinearSpectralRadiusLtOne (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Prop :=
  ∃ G : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ G i j) ∧
    (∀ s : Fin n → ℝ≥0, (fun i => (T s i : ℝ)) = G.mulVec (fun j => (s j : ℝ))) ∧
    ∀ z ∈ spectrum ℂ (G.map (algebraMap ℝ ℂ)), ‖z‖ < 1

/-- A cycle in `Γ` (§8.4, p. 27): indices `i₁, …, i_K` (`K = m + 1 ≥ 1`, here `c 0, …, c m`)
such that every entry `γ_{i₁,i₂}, γ_{i₂,i₃}, …, γ_{i_K,i₁}` is nonzero. -/
def IsCycle (Γ : SmallGainISS.Lyapunov.GainMatrix n) {m : ℕ} (c : Fin (m + 1) → Fin n) : Prop :=
  ∀ k, Γ (c k) (c (finRotate (m + 1) k)) ≠ 0

/-- A cycle is subordinated if `i₁ > max{i₂, …, i_K}`. -/
def IsSubordinated {m : ℕ} (c : Fin (m + 1) → Fin n) : Prop :=
  ∀ k : Fin (m + 1), k ≠ 0 → c k < c 0

/-- The cycle gain `γ_{i₁,i₂} ∘ γ_{i₂,i₃} ∘ … ∘ γ_{i_K,i₁}`. -/
def cycleGain (Γ : SmallGainISS.Lyapunov.GainMatrix n) {m : ℕ} (c : Fin (m + 1) → Fin n) : ℝ≥0 → ℝ≥0 :=
  (List.ofFn fun k : Fin (m + 1) => Γ (c k) (c (finRotate (m + 1) k))).foldr (· ∘ ·) id

/-- A cycle is a contraction if its cycle gain is `< id`, i.e. `< r` at every `r > 0`. -/
def IsContraction (Γ : SmallGainISS.Lyapunov.GainMatrix n) {m : ℕ} (c : Fin (m + 1) → Fin n) : Prop :=
  ∀ r, 0 < r → cycleGain Γ c r < r

/-- All subordinated cycles of `Γ` are contractions (Theorem 8.14). -/
def SubordinatedCyclesContract (Γ : SmallGainISS.Lyapunov.GainMatrix n) : Prop :=
  ∀ (m : ℕ) (c : Fin (m + 1) → Fin n), IsCycle Γ c → IsSubordinated c → IsContraction Γ c

end SmallGainISS.OmegaPath


