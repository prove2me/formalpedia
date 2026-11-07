-- Prove2me | Definitions.Def_SYKCavity_Majorana
-- name    : SYKCavity_Majorana
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:46.573195+00:00
-- url     : https://prove2.me/theorems/aa02ddcf-8261-4989-934d-6db0f53d72ed
-- title:
--   Majorana fermions, the SYK Hamiltonian $H$, weight-$w$ observables and $f_O(\beta,J)=\mathrm{Tr}(Oe^{\beta H})/\mathrm{Tr}\,e^{\beta H}$
-- statement:
--   Let $N\ge1$. The **Majorana fermions** $\psi_0,\dots,\psi_{N-1}$ are Hermitian matrices with $\{\psi_i,\psi_j\}=2\delta_{ij}I$; here they are the first $N$ Jordan–Wigner generators on $\lceil N/2\rceil$ qubits,
--   $$\psi_{2k}=Z^{\otimes k}\otimes X\otimes I\otimes\cdots,\qquad \psi_{2k+1}=Z^{\otimes k}\otimes Y\otimes I\otimes\cdots.$$
--   For a set $A$ of sites write $\psi_A=\prod^{\nearrow}_{i\in A}\psi_i$ (increasing order) and $\Gamma_A=i^{|A|(|A|-1)/2}\psi_A$ (3.1). With independent standard Gaussian couplings $J_A$, one for each $4$-subset $A$ of the sites, the SYK Hamiltonian is
--   $$H=\sqrt{\tfrac{3}{8N^3}}\sum_{i_1<i_2<i_3<i_4}J_{i_1i_2i_3i_4}\psi_{i_1}\psi_{i_2}\psi_{i_3}\psi_{i_4}\qquad(1.2)$$
--   and, in Section 3's form, $H_\Gamma=\sqrt{3/(8N^3)}\sum_AJ_A\Gamma_A$. Since $\Gamma_A=-\psi_A$ for $|A|=4$, $H_\Gamma(J)=H(-J)$, and the Gaussian law is invariant under $J\mapsto-J$.
--
--   For sites $i_1<\dots<i_w$ the weight-$w$ observable is $O=i^{w(w-1)/2}\psi_{i_1}\cdots\psi_{i_w}$, and the thermal expectation of Theorem 2 is
--   $$f_O(\beta,J)=\frac{\operatorname{Tr}(Oe^{\beta H})}{\operatorname{Tr}e^{\beta H}}.$$
--   The file also fixes $e^{s\beta H}$ for both forms of $H$ and the coupling law $\bigotimes_A N(0,1)$.
--
--   These are the objects of every statement of the mission: the goal uses (1.2), the milestones use Section 3's $H_\Gamma$.
--
--   **Formalization Note** Sites are `Fin N` (0-based); a coupling vector is a function on the $4$-subsets. For odd $N$ one Jordan–Wigner generator of the $\lceil N/2\rceil$-qubit register is unused. Matrix exponentials are `NormedSpace.exp`; $f_O$ is kept as a complex number (it is real for Hermitian $O$).
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (1.2), p.4; Theorem 2, pp.4–5; (3.1), p.20; p.22 (Γ_A = −ψ_A for |A| = 4)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana

open MeasureTheory ProbabilityTheory

namespace SYKCavity

/-!
# Majorana fermions, the SYK Hamiltonian, weight-`w` observables and the thermal ratio

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): model (1.2), p.4; Theorem 2,
pp.4–5; conventions (3.1), p.20; the remark `Γ_A = −ψ_A` for `|A| = 4`, p.22.

**Formalization Note.**
* The Majoranas `ψ_0, …, ψ_{N−1}` are the first `N` Jordan–Wigner generators on `⌈N/2⌉ = (N+1)/2`
  qubits, the published `FermiCap.Gaussian.majorana` (`2k ↦ Z^{⊗k} ⊗ X ⊗ 1`,
  `2k+1 ↦ Z^{⊗k} ⊗ Y ⊗ 1`). They are Hermitian, square to `1` and pairwise anticommute, i.e.
  `{ψ_i, ψ_j} = 2δ_ij I`. For odd `N` one generator of the register is left unused.
* Sites are `Fin N` (the page's `[N]` shifted to start at `0`); a coupling index is a 4-subset
  `A ⊆ Fin N` (`Quad N`), and a coupling vector is `J : Quad N → ℝ`.
* `orderedProd N A = ∏↗_{i ∈ A} ψ_i` in increasing site order; `Gamma N A = i^{|A|(|A|−1)/2} ψ_A`
  is (3.1).
* `H12 N J` is (1.2): `√(3/(8N³)) Σ_A J_A ψ_A`. `Hgamma N J` is Section 3's form
  `√(3/(8N³)) Σ_A J_A Γ_A`. Since `Γ_A = −ψ_A` for `|A| = 4`, `Hgamma N J = H12 N (−J)`; the
  Gaussian law is invariant under `J ↦ −J` (p.20).
* `obs N idx` is `O = i^{w(w−1)/2} ψ_{i_1} ⋯ ψ_{i_w}` with `i_1 < ⋯ < i_w` given by an order
  embedding `idx : Fin w ↪o Fin N`.
* `gaussLaw N` is the product of standard Gaussians `N(0,1)` over the 4-subsets.
* `expH β N J s = e^{sβH}` for Section 3's `H` (`Hgamma`), `expH12 β N J s` for (1.2)'s `H`;
  matrix exponentials are `NormedSpace.exp` on complex matrices.
* `fO β N O J = Tr(O e^{βH}) / Tr e^{βH}` (Theorem 2) with (1.2)'s `H`, as a complex number; for
  Hermitian `O` it is real.
-/

open FermiCap.Gaussian

/-- The number of qubits carrying `N` Majoranas: `⌈N/2⌉`. -/
def nq (N : ℕ) : ℕ := (N + 1) / 2

/-- Operators on the `⌈N/2⌉`-qubit register. -/
abbrev MOp (N : ℕ) := FermiCap.Gaussian.Op (nq N)

/-- The Majorana `ψ_i`, `i ∈ Fin N`: the `i`-th Jordan–Wigner generator on `⌈N/2⌉` qubits. -/
noncomputable def psi (N : ℕ) (i : Fin N) : MOp N :=
  majorana (nq N) ⟨i.val, by unfold nq; omega⟩

/-- The 4-subsets of the sites, indexing the couplings `J_A`. -/
abbrev Quad (N : ℕ) := {A : Finset (Fin N) // A.card = 4}

/-- `ψ_A = ∏↗_{i ∈ A} ψ_i`, the product in increasing site order. -/
noncomputable def orderedProd (N : ℕ) (A : Finset (Fin N)) : MOp N :=
  ((A.sort (· ≤ ·)).map (psi N)).prod

/-- The canonically ordered Majorana string `Γ_A = i^{|A|(|A|−1)/2} ψ_A`, (3.1). -/
noncomputable def Gamma (N : ℕ) (A : Finset (Fin N)) : MOp N :=
  (Complex.I ^ (A.card * (A.card - 1) / 2)) • orderedProd N A

/-- The SYK coupling scale `√(3/(8N³))`. -/
noncomputable def scale (N : ℕ) : ℝ := Real.sqrt (3 / (8 * (N : ℝ) ^ 3))

/-- The SYK Hamiltonian in the form (1.2), p.4: `H = √(3/(8N³)) Σ_{i₁<i₂<i₃<i₄} J ψ_{i₁}ψ_{i₂}ψ_{i₃}ψ_{i₄}`. -/
noncomputable def H12 (N : ℕ) (J : Quad N → ℝ) : MOp N :=
  ((scale N : ℝ) : ℂ) • ∑ A : Quad N, ((J A : ℝ) : ℂ) • orderedProd N A.1

/-- The SYK Hamiltonian in Section 3's form, p.20: `H = √(3/(8N³)) Σ_A J_A Γ_A`. -/
noncomputable def Hgamma (N : ℕ) (J : Quad N → ℝ) : MOp N :=
  ((scale N : ℝ) : ℂ) • ∑ A : Quad N, ((J A : ℝ) : ℂ) • Gamma N A.1

/-- The weight-`w` observable `O = i^{w(w−1)/2} ψ_{i_1} ⋯ ψ_{i_w}`, `i_1 < ⋯ < i_w`. -/
noncomputable def obs (N : ℕ) {w : ℕ} (idx : Fin w ↪o Fin N) : MOp N :=
  (Complex.I ^ (w * (w - 1) / 2)) • ((List.finRange w).map (fun k => psi N (idx k))).prod

/-- The coupling law: independent standard Gaussians `J_A ~ N(0,1)`, one per 4-subset. -/
noncomputable def gaussLaw (N : ℕ) : Measure (Quad N → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- `e^{sβH}` for Section 3's Hamiltonian `H = Hgamma N J`. -/
noncomputable def expH (β : ℝ) (N : ℕ) (J : Quad N → ℝ) (s : ℝ) : MOp N :=
  NormedSpace.exp (((s * β : ℝ) : ℂ) • Hgamma N J)

/-- `e^{sβH}` for the Hamiltonian (1.2), `H = H12 N J`. -/
noncomputable def expH12 (β : ℝ) (N : ℕ) (J : Quad N → ℝ) (s : ℝ) : MOp N :=
  NormedSpace.exp (((s * β : ℝ) : ℂ) • H12 N J)

/-- `f_O(β, J) = Tr(O e^{βH}) / Tr e^{βH}` for the Hamiltonian (1.2) (Theorem 2, p.4). -/
noncomputable def fO (β : ℝ) (N : ℕ) (O : MOp N) (J : Quad N → ℝ) : ℂ :=
  (O * expH12 β N J 1).trace / (expH12 β N J 1).trace

end SYKCavity


