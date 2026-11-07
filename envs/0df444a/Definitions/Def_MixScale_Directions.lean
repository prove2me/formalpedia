-- Prove2me | Definitions.Def_MixScale_Directions
-- name    : MixScale_Directions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:45.065175+00:00
-- url     : https://prove2.me/theorems/1d73946e-9d72-4ba0-8403-ef58d6e5d4d7
-- title:
--   The direction families (43), the designs (46) and the geometric event of Lemma D.1
-- statement:
--   With $g,g'\sim N(0,I_d)$ independent, let $u=g/\|g\|$, $\Delta_A=\gamma/(10^4k^2\sqrt d)$, $h=\Delta_A/(16B)$, $z=g'/(1000d^2)$ and $\Delta_T=\gamma/(10^7k^2d^4)$. The anchor family is $\{u,u+he_1,\dots,u+he_d\}$; the stable family is $\{e_i+z\}\cup\{e_i+e_j+z:i<j\}$.
--
--   With rows indexed by the stable directions $p$, the design $P$ has row $p^\top$ and the design $Q$ has row $(p_a^2)_a$ followed by $(\sqrt2p_ap_b)_{a<b}$, so that $Q\,\mathrm{svec}(A)=(p^\top Ap)_p$ for symmetric $A$, where $\mathrm{svec}(A)=(A_{aa})_a$ followed by $(\sqrt2A_{ab})_{a<b}$.
--
--   The event $G$ collects clauses 1–3 of Lemma D.1: $|u^\top(\mu_j-\mu_\ell)|\ge4\Delta_A$, $|p^\top(\mu_j-\mu_\ell)|\ge4\Delta_T$ for each stable $p$, and $\|z\|\le1/(100d^{3/2})$.
--
--   These objects let the algorithm reduce recovery in $\mathbb R^d$ to scalar projections and then reassemble centers and scale matrices.
--
--   **Formalization Note** $N(0,I_d)$ is the image of the product of standard Gaussians. The default direction for $g=0$ is $e_0$ (0-based coordinates). Rows are indexed by singletons, then pairs; least squares, singular values and Euclidean norms do not depend on the row order.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), §D.1, (43), p.25 (PDF p.27); Lemma D.1, p.25; §D.3, p.26 and (46), p.27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_MixScale_Model

open MeasureTheory ProbabilityTheory

namespace MixScale

/-!
# The two random direction families (43) and the reconstruction designs (46)

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). §D.1, (43), p.25 (PDF p.27); §D.3, svec
p.26 and (46), p.27 (PDF pp.28–29).

"Let `g, g′ ∼ N(0, I_d)` be independent of the sample batches. Define `u = g/‖g‖`,
`Δ_A = γ/(10⁴k²√d)`, `h = Δ_A/(16B)`, `z = g′/(1000d²)`, `Δ_T = γ/(10⁷k²d⁴)`. (43) The anchor family
is `U_A = {u, u + he₁, …, u + he_d}`. The stable measurement family is
`U_T = {e_i + z : 1 ≤ i ≤ d} ∪ {e_i + e_j + z : 1 ≤ i < j ≤ d}`. […] Null Gaussian vectors are
assigned a fixed default direction." "`svec(A) = (A₁₁, …, A_dd, √2A₁₂, …, √2A_{d−1,d})⊤`." (46): the
rows of `P` are the stable directions `p`, and the row of `Q` at `p` is
`(p₁², …, p_d², √2p₁p₂, …, √2p_{d−1}p_d)`.

**Formalization Note.**
* `N(0, I_d)` on `ℝ^d` is the image of `Π_{i<d} N(0, 1)` under `WithLp.toLp 2` (`stdGaussian`).
* The default direction for `g = 0` is `e₀` (0-based coordinates), and `0` in dimension `0`.
* The stable family and the coordinates of `svec` are indexed by `StableIdx d = Fin d ⊕ {(i, j) :
  i < j}`: singletons first, then pairs. Least squares, singular values and Euclidean norms do not
  depend on the order of the rows; `l2` is the Euclidean norm on `ι → ℝ`.
-/

/-- The standard Gaussian `N(0, I_d)` on `ℝ^d`. -/
noncomputable def stdGaussian (d : ℕ) : Measure (Vec d) :=
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).map (WithLp.toLp 2)

/-- The `i`-th standard basis vector `e_i`. -/
noncomputable def basisVec {d : ℕ} (i : Fin d) : Vec d := EuclideanSpace.single i 1

/-- The fixed default direction `e₀` (and `0` if `d = 0`). -/
noncomputable def defaultDir (d : ℕ) : Vec d :=
  if h : 0 < d then EuclideanSpace.single ⟨0, h⟩ 1 else 0

/-- `u = g/‖g‖`, with the default direction for `g = 0`. -/
noncomputable def unitDir {d : ℕ} (g : Vec d) : Vec d :=
  if g = 0 then defaultDir d else ‖g‖⁻¹ • g

/-- `Δ_A = γ/(10⁴ k² √d)` (43). -/
noncomputable def DeltaA (γ : ℝ) (k d : ℕ) : ℝ := γ / (10 ^ 4 * (k : ℝ) ^ 2 * Real.sqrt d)

/-- `h = Δ_A/(16B)` (43). -/
noncomputable def stepH (γ B : ℝ) (k d : ℕ) : ℝ := DeltaA γ k d / (16 * B)

/-- `z = g′/(1000 d²)` (43). -/
noncomputable def pertZ {d : ℕ} (g' : Vec d) : Vec d := (1000 * (d : ℝ) ^ 2)⁻¹ • g'

/-- `Δ_T = γ/(10⁷ k² d⁴)` (43). -/
noncomputable def DeltaT (γ : ℝ) (k d : ℕ) : ℝ := γ / (10 ^ 7 * (k : ℝ) ^ 2 * (d : ℝ) ^ 4)

/-- The anchor family `U_A`: `u` (index `none`) and `u + h e_i` (index `some i`). -/
noncomputable def anchorDir {d : ℕ} (γ B : ℝ) (k : ℕ) (g : Vec d) : Option (Fin d) → Vec d
  | none => unitDir g
  | some i => unitDir g + stepH γ B k d • basisVec i

/-- Index set of the stable directions and of the `svec` coordinates: singletons, then pairs
`i < j`. -/
abbrev StableIdx (d : ℕ) := Fin d ⊕ {p : Fin d × Fin d // p.1 < p.2}

/-- The stable direction `e_i + z` (singleton `i`) or `e_i + e_j + z` (pair `i < j`). -/
noncomputable def stableDir {d : ℕ} (z : Vec d) : StableIdx d → Vec d
  | .inl i => basisVec i + z
  | .inr p => basisVec p.1.1 + basisVec p.1.2 + z

/-- The linear design `P` of (46): the row at `p` is `p⊤`. -/
noncomputable def designP {d : ℕ} (z : Vec d) : Matrix (StableIdx d) (Fin d) ℝ :=
  fun p a => stableDir z p a

/-- The quadratic design `Q` of (46): the row at `p` is `(p_a²)_a` followed by `(√2 p_a p_b)_{a<b}`. -/
noncomputable def designQ {d : ℕ} (z : Vec d) : Matrix (StableIdx d) (StableIdx d) ℝ :=
  fun p c => match c with
    | .inl a => stableDir z p a ^ 2
    | .inr ab => Real.sqrt 2 * stableDir z p ab.1.1 * stableDir z p ab.1.2

/-- `svec(A) = (A_aa)_a` followed by `(√2 A_ab)_{a<b}`. -/
noncomputable def svec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : StableIdx d → ℝ
  | .inl a => A a a
  | .inr ab => Real.sqrt 2 * A ab.1.1 ab.1.2

/-- The symmetric matrix with `svec` coordinates `y` (the inverse of `svec` on symmetric
matrices). -/
noncomputable def svecInv {d : ℕ} (y : StableIdx d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b =>
    if hab : a < b then y (.inr ⟨(a, b), hab⟩) / Real.sqrt 2
    else if hba : b < a then y (.inr ⟨(b, a), hba⟩) / Real.sqrt 2
    else y (.inl a)

/-- The event `G` of Lemma D.1 as a set of pairs `(g, g′)`, depending only on the directions and the
centers `μ`: clause 1 `|u⊤(μ_j − μ_ℓ)| ≥ 4Δ_A`, clause 2 `|p⊤(μ_j − μ_ℓ)| ≥ 4Δ_T` for every stable
direction `p`, clause 3 `‖z‖ ≤ 1/(100 d^{3/2})`. -/
def GeoEvent {d k : ℕ} (γ : ℝ) (μ : Fin k → Vec d) : Set (Vec d × Vec d) :=
  {x | (∀ j l, j ≠ l → 4 * DeltaA γ k d ≤ |inner ℝ (unitDir x.1) (μ j - μ l)|) ∧
    (∀ (p : StableIdx d) (j l : Fin k), j ≠ l →
      4 * DeltaT γ k d ≤ |inner ℝ (stableDir (pertZ x.2) p) (μ j - μ l)|) ∧
    ‖pertZ x.2‖ ≤ 1 / (100 * (d : ℝ) ^ (3 / 2 : ℝ))}

/-- The Euclidean norm of a real vector indexed by a finite type. -/
noncomputable def l2 {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := Real.sqrt (∑ i, y i ^ 2)

end MixScale


