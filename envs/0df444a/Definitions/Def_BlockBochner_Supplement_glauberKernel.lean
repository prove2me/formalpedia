-- Prove2me | Definitions.Def_BlockBochner_Supplement_glauberKernel
-- name    : BlockBochner_Supplement_glauberKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:29:32.449678+00:00
-- url     : https://prove2.me/theorems/46189391-a631-4434-836c-ba34bf3d0487
-- title:
--   Glauber dynamics transition kernel $P_{\mathrm{Glaub}}$ of the $O(N)$ model
-- statement:
--   Glauber dynamics of $\mu_{J,h}$ moves from a configuration $\sigma$ as follows: choose a site $x\in V$ uniformly at random and replace $\sigma_x$ by a fresh sample from the conditional law of $\sigma_x$ given $\sigma_{V\setminus\{x\}}$. For the $O(N)$ measure with symmetric zero-diagonal $J$ that conditional law is the tilted Haar measure
--   $$
--   \nu_{h_x+\sum_{y\ne x}J_{xy}\sigma_y}(du)\ \propto\ \exp\Big(\big(h_x+\textstyle\sum_{y\ne x}J_{xy}\sigma_y\big)\cdot u\Big)\,d\omega(u).
--   $$
--   So
--   $$
--   P_{\mathrm{Glaub}}(\sigma,\cdot)=\frac1{|V|}\sum_{x\in V}\mathrm{Law}\big(\sigma\text{ with }\sigma_x\text{ replaced by }U\big),\qquad U\sim\nu_{h_x+\sum_{y\ne x}J_{xy}\sigma_y}.
--   $$
--
--   This kernel, defined at every configuration, is the chain whose mixing time Theorem 5 bounds.
--
--   **Formalization Note** A Markov kernel (`ProbabilityTheory.Kernel`) on $(S^{N-1})^V$: for each site, $\omega$ with density $|V|^{-1}\,d\nu/d\omega$ paired with the current configuration and pushed forward by the update map, summed over the sites. The explicit tilted-Haar version of the conditional law is used so that $P_{\mathrm{Glaub}}(\sigma,\cdot)$ is defined at every $\sigma$ (the mixing time takes a supremum over all starting configurations). The verification file proves the density and the update map measurable, so Mathlib's constructors do not return their junk value $0$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.1, p.2 (PDF p.3); Sec. 4.1, p.27 (PDF p.28); Sec. 4.2, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_tiltedDensity

open MeasureTheory ProbabilityTheory

namespace BlockBochner.Supplement

/-- **O(N) Glauber transition kernel `P_Glaub`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.1, p.2 ("choose
a uniformly random vertex and forget its spin. Then, sample a new spin for that vertex according to
the µ-conditional distribution") and Sec. 4.1, p.27 (the conditional law of a spin given the others
is a tilted Haar measure). From the configuration `σ`, a site `x ∈ V` is chosen uniformly and `σ_x`
is replaced by a sample of
```
ν_{h_x + Σ_{y≠x} J_xy σ_y}(du) ∝ exp((h_x + Σ_{y≠x} J_xy σ_y)·u) dω(u),
```
which is the conditional law of `σ_x` given `σ_{V∖{x}}` under `µ_{J,h}` when `J` is symmetric with
zero diagonal. So `P_Glaub(σ, ·) = (1/|V|) Σ_x (law of σ with σ_x replaced by u ∼ ν_{field_x(σ)})`.

**Formalization Note** A Markov kernel (`ProbabilityTheory.Kernel`) defined at **every**
configuration `σ` (the mixing time takes a supremum over all starting points). For each site `x`
the resampling kernel is `ω` with density `|V|⁻¹ · dν_{field_x(σ)}/dω`, paired with the identity and
pushed forward by `(σ, u) ↦ σ[x ↦ u]`; the `|V|⁻¹` weight inside the density realizes the uniform
choice of the site, and the kernels are summed over `x`. (The Mathlib constructors `withDensity`
and `map` return `0` on non-measurable data; the data here is continuous, hence measurable.) -/
noncomputable def glauberKernel (N : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (J : Matrix V V ℝ) (h : V → EuclideanSpace ℝ (Fin N)) : Kernel (V → GraphNNSphere.Sph N) (V → GraphNNSphere.Sph N) :=
  ∑ x : V, Kernel.map
    (Kernel.id ×ₖ Kernel.withDensity (Kernel.const (V → GraphNNSphere.Sph N) (haarSphere N))
      (fun σ u => (((Fintype.card V : NNReal)⁻¹ * tiltedDensity N
        (h x + ∑ y ∈ Finset.univ.erase x, J x y • (σ y : EuclideanSpace ℝ (Fin N))) u : NNReal) :
          ENNReal)))
    (fun p => Function.update p.1 x p.2)

end BlockBochner.Supplement


