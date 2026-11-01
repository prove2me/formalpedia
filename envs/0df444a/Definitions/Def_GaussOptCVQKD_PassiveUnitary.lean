-- Prove2me | Definitions.Def_GaussOptCVQKD_PassiveUnitary
-- name    : GaussOptCVQKD_PassiveUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:21.193889+00:00
-- url     : https://prove2.me/theorems/4bd2e989-d431-4377-96b8-77d36b995f39
-- title:
--   Local passive unitaries implementing a real orthogonal mode mixing, and invariance under them
-- statement:
--   **Passive orthogonal unitaries (p.2).** A unitary $U$ on the Fock space of modes $J$ *implements* a real orthogonal matrix $O$ if
--   $$
--   U^\dagger W(\xi)\,U=W(\xi'),\qquad \xi'(i,k)=\sum_j O_{ij}\,\xi(j,k)\quad(k\in\{x,p\}),
--   $$
--   for every Weyl operator, i.e. $U^\dagger R_{j,k}U=\sum_i O_{ij}R_{i,k}$: the same real orthogonal mixing of the $x$ quadratures and of the $p$ quadratures. "The Gaussification unitary $U_G$ is a passive operation … the $x$ and $p$ quadratures of all $N$ modes are thus not mixed via Gaussification."
--
--   **Local family.** Alice and Bob each apply such a unitary to their own modes.
--
--   **Invariance.** A functional $f$ of labelled bipartite oscillator states is *passively invariant* on a domain if it is unchanged by every local family of passive orthogonal unitaries and by every owner-preserving relabelling of the modes, whenever both states lie in the domain.
--
--   **Formalization Note** The Weyl-covariance pattern is that of the published copy mixers (Support50.P14); $O$ ranges over Mathlib's `Matrix.orthogonalGroup`. The relabelling clause is copied from Support50.P14 `LocallyInvariant`.
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Extremality of Gaussian states' p.2 (after (5)) and property ii) p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel boundedUnitaryConjugation)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel InterleavedQuadrature oscillatorWeylKernel localKernel InDomain MultipartiteOscillatorFunctional)

namespace GaussOptCVQKD

open Classical in
/-- **A passive unitary that mixes modes by a real orthogonal matrix**, García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, "Extremality of Gaussian states", p.2: "The Gaussification unitary U_G
is a passive operation, which can be realized with a network of beam splitters and phase shifters.
Importantly for what follows, the x and p quadratures of all N modes are thus not mixed via
Gaussification."

`U` (a bounded unitary on the Fock space of the modes `J`) implements the real orthogonal
matrix `O`: `U† W(ξ) U = W(ξ')` for every Weyl operator, with `ξ'(i, k) = Σ_j O_{i j} ξ(j, k)`
for both quadratures `k = x, p`. Equivalently `U† R_{j,k} U = Σ_i O_{i j} R_{i,k}`: the same real
orthogonal mixing of the `x` quadratures and of the `p` quadratures.

**Formalization Note** Same Weyl-covariance pattern as the copy mixers of the published
Support50.P14 (`localGaussification`); `O` ranges over Mathlib's `Matrix.orthogonalGroup`. -/
def ImplementsOrthogonal {J : Type} [Fintype J]
    (U : Hilbert (Occupation J) ≃ₗᵢ[ℂ] Hilbert (Occupation J)) : Prop :=
  ∃ O ∈ Matrix.orthogonalGroup J ℝ, ∀ ξ : InterleavedQuadrature J → ℝ,
    boundedUnitaryConjugation U.symm (oscillatorWeylKernel ξ) =
      oscillatorWeylKernel (fun r => ∑ i, O i r.1 * ξ (i, r.2))

/-- **Local Gaussification-type unitaries**: each party `p` applies a passive unitary `U p` on
its own modes that implements a real orthogonal mixing of them (`ImplementsOrthogonal`).
The Gaussification operation `U_G ⊗ U_G` of p.2 (Alice's `U_G` on her copies, Bob's on his) is of
this kind. -/
def LocalPassiveOrthogonal {I : Type} [Fintype I] (owner : I → Fin 2)
    (U : (p : Fin 2) → Hilbert (Occupation {j : I // owner j = p}) ≃ₗᵢ[ℂ]
      Hilbert (Occupation {j : I // owner j = p})) : Prop :=
  ∀ p, ImplementsOrthogonal (U p)

/-- **Invariance under local passive orthogonal unitaries**, the form in which property ii) of
García-Patrón, Cerf, arXiv:quant-ph/0608032v1, p.3 ("we obtain the invariance of K(ρAB) under
local Gaussification unitaries") is established for the key rate.

A functional family `f` (Support50.P14 `MultipartiteOscillatorFunctional 2`) is unchanged
(1) by every family of local passive orthogonal unitaries (`LocalPassiveOrthogonal`) and
(2) by every owner-preserving relabelling of the modes,
whenever both states lie in the domain `InDomain cap` (all densities for `cap = none`, the
densities of mean photon number at most `e` per mode for `cap = some e`).

**Formalization Note** Clause (2) is the second clause of Support50.P14 `LocallyInvariant`
verbatim; clause (1) replaces its invariance under *all* local unitaries by invariance under the
passive orthogonal ones, which contain the Gaussification unitaries `U_G ⊗ U_G`. -/
def PassiveInvariant (cap : Option ℝ) (f : MultipartiteOscillatorFunctional 2) : Prop :=
  (∀ (I : Type) [Fintype I] (owner : I → Fin 2) (rho : OscillatorKernel I)
    (U : (p : Fin 2) → Hilbert (Occupation {j : I // owner j = p}) ≃ₗᵢ[ℂ]
      Hilbert (Occupation {j : I // owner j = p})),
    LocalPassiveOrthogonal owner U →
    InDomain cap rho → InDomain cap (conjugateKernel (localKernel owner U) rho) →
    f I owner (conjugateKernel (localKernel owner U) rho) = f I owner rho) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] (e : I ≃ J)
    (owner : J → Fin 2) (rho : OscillatorKernel I), InDomain cap rho →
    InDomain cap (fun u v => rho (u ∘ e) (v ∘ e)) →
    f J owner (fun u v => rho (u ∘ e) (v ∘ e)) = f I (owner ∘ e) rho)

end GaussOptCVQKD


