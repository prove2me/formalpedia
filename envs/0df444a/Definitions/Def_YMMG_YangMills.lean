-- Prove2me | Definitions.Def_YMMG_YangMills
-- name    : YMMG_YangMills
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T16:32:05.576233+00:00
-- url     : https://prove2.me/theorems/7d0691bc-52d1-4a9e-911d-90e13af62729
-- title:
--   Non-trivial quantum Yang–Mills theory with gauge group $G$ (proxy definition)
-- statement:
--   $Q$ is a **non-trivial quantum Yang–Mills theory with gauge group $(G,\rho)$** if the following holds. There is a Lorentz-scalar field component $\varphi_{i,c}$ of $Q$ (playing the role of $\operatorname{tr}F_{\mu\nu}F^{\mu\nu}$) with three properties:
--
--   - it is not a generalized free field;
--   - its Wightman distributions $\mathfrak W$ have a Euclidean restriction $\mathfrak S$;
--   - $\mathfrak S$ is a continuum scaling limit of the renormalized plaquette field of Wilson's lattice gauge theory for $(G,\rho)$.
--
--   **This is a proxy, and it needs review.** The source asks for local fields that correspond to all gauge-invariant local polynomials in the curvature and whose short-distance behaviour matches asymptotic freedom and perturbative renormalization. That requirement has no standard mathematical formulation.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §4 (the problem statement) and §6.5

module

public import Mathlib
public import Definitions.Def_YMMG_WightmanQFT
public import Definitions.Def_YMMG_Lattice

/-!
# What it means for a Wightman QFT to be a quantum Yang–Mills theory with gauge group `G`

Jaffe–Witten (§4) ask for local quantum fields in correspondence with the gauge-invariant local
polynomials in the curvature, whose correlations agree at short distances with asymptotic
freedom. That correspondence has no standard mathematical definition. This draft uses the
following **proxy** (to be reviewed): the theory contains a Lorentz-scalar field component —
playing the role of `tr F_{μν}F^{μν}` — which is non-trivial (not a generalized free field) and
whose Schwinger functions are a continuum scaling limit (`a → 0`, volume `→ ∞`, `β → ∞`) of the
renormalized plaquette field of Wilson's lattice gauge theory with gauge group `G`.
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

/-- `Q` is a **non-trivial quantum Yang–Mills theory with gauge group `(G, ρ)`** (proxy
definition, see module docstring): there is a Lorentz-scalar field component `φ_{i,c}` of `Q`
which is not a generalized free field, with Wightman distributions `𝔚` and Schwinger functions
`𝔖` (the Euclidean restriction of the analytic continuation of `𝔚`), such that `𝔖` is a
continuum scaling limit of the renormalized plaquette field of Wilson's lattice gauge theory
for `(G, ρ)`. -/
def IsNontrivialYangMillsTheory {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type} {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (Q : WightmanQFT H ι κ)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}
    (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) : Prop :=
  ∃ (i : ι) (c : κ i) (W S : DistributionFamily),
    Q.IsScalarMultiplet i ∧ ¬ Q.IsGeneralizedFreeField i c ∧
    Q.IsWightmanFamilyOf i c W ∧ IsEuclideanRestriction W S ∧ IsWilsonScalingLimit ρ S

end YangMillsMassGap

end


