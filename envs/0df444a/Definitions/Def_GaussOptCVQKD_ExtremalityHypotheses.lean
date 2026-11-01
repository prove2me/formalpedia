-- Prove2me | Definitions.Def_GaussOptCVQKD_ExtremalityHypotheses
-- name    : GaussOptCVQKD_ExtremalityHypotheses
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:22.265234+00:00
-- url     : https://prove2.me/theorems/019d38e8-3b67-4bce-b13e-8a87f2145f33
-- title:
--   Hypotheses 2 and 3 of the Gaussian extremality theorem: Gaussification invariance and strong super-additivity
-- statement:
--   **Hypothesis 2 (p.2).** "invariance under local 'Gaussification' unitaries: $f(U_G^\dagger\otimes U_G^\dagger\,\rho_{AB}^{\otimes N}\,U_G\otimes U_G)=f(\rho_{AB}^{\otimes N})$". Here $N=2^m$, $U_G$ is the Wolf–Giedke–Cirac Gaussification unitary on the $N$ copies of one mode (the Sylvester–Hadamard mixing $H^{\otimes m}/\sqrt{2^m}$ of the copies, the same on $x$ and $p$), applied to the copies of every mode; copies keep the owner of their mode. In addition $f$ is unchanged by owner-preserving relabellings of the modes.
--
--   **Hypothesis 3 (p.2), two copies.** "strong super-additivity: $f(\rho_{A_{1\ldots N}B_{1\ldots N}})\ge f(\rho_{A_1B_1})+\dots+f(\rho_{A_NB_N})$ with equality if $\rho_{A_{1\ldots N}B_{1\ldots N}}=\rho_{A_1B_1}\otimes\dots\otimes\rho_{A_NB_N}$", stated for $N=2$: for every system $A_kB_k$ (a finite mode set with owners) and every state $\rho$ of two copies of it,
--   $$
--   f(\rho_1)+f(\rho_2)\le f(\rho),\qquad f(\rho_1\otimes\rho_2)=f(\rho_1)+f(\rho_2),
--   $$
--   with $\rho_1,\rho_2$ the two block marginals.
--
--   Both clauses are required only for states in a given domain (all densities, or an energy sublevel).
--
--   **Formalization Note** $U_G$, its Weyl covariance, tensor powers and copy mixers are the published Support50.P14 objects (`mixedArgument`, `copiesKernel`, `copyMixerKernel`). The relabelling clause encodes that the paper's $f$ is a function of the bipartite state and does not see mode labels.
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Extremality of Gaussian states', hypotheses 2 and 3, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel boundedUnitaryConjugation)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel oscillatorWeylKernel InDomain MultipartiteOscillatorFunctional mixedArgument copiesKernel copyMixerKernel marginalFirst marginalSecond oscillatorTensor)

namespace GaussOptCVQKD

/-- **Hypothesis 2 of the extremality theorem: invariance under local “Gaussification”
unitaries**, García-Patrón, Cerf, *Unconditional optimality of Gaussian attacks against
continuous-variable QKD*, arXiv:quant-ph/0608032v1, "Extremality of Gaussian states", p.2:
"2. invariance under local “Gaussification” unitaries: f(U_G† ⊗ U_G† ρ_AB^⊗N U_G ⊗ U_G) =
f(ρ_AB^⊗N)", with (5): "The Gaussification unitary U_G is a passive operation … the x and p
quadratures of all N modes are thus not mixed via Gaussification."

For a functional family `f` (Support50.P14 `MultipartiteOscillatorFunctional 2`) and a domain
`cap`:
(1) for every state `ρ` on the modes `I` (owner map `owner`), every `m` and every bounded unitary
`U` on the `N = 2^m` copies of one mode that implements the Gaussification (Sylvester–Hadamard)
mixing of Wolf–Giedke–Cirac (`U† W(ξ) U = W(mixedArgument m ξ)`), applying `U` to the copies of
every mode (`copyMixerKernel`, i.e. `U_G` at Alice's and at Bob's side) does not change
`f(ρ^{⊗N})`; the copies of a mode keep that mode's owner;
(2) `f` is unchanged by every owner-preserving relabelling of the modes,
whenever the states involved lie in `InDomain cap`.

**Formalization Note** The Gaussification unitary, its Weyl covariance `mixedArgument`, the
tensor power `copiesKernel` and the copy mixer `copyMixerKernel` are the published Support50.P14
objects. Clause (2) is the encoding of "f is a function of the bipartite state": the paper's `f`
does not see mode labels, while a functional of labelled modes must be told so (it is the
second clause of Support50.P14 `LocallyInvariant`). -/
def GaussificationInvariant (cap : Option ℝ) (f : MultipartiteOscillatorFunctional 2) : Prop :=
  (∀ (I : Type) [Fintype I] (owner : I → Fin 2) (rho : OscillatorKernel I) (m : ℕ)
    (U : Hilbert (Occupation (Copies Bool m)) ≃ₗᵢ[ℂ] Hilbert (Occupation (Copies Bool m))),
    (∀ xi, boundedUnitaryConjugation U.symm (oscillatorWeylKernel xi) =
      oscillatorWeylKernel (mixedArgument m xi)) →
    InDomain cap rho → InDomain cap (copiesKernel m rho) →
    InDomain cap (conjugateKernel (copyMixerKernel m U) (copiesKernel m rho)) →
    f (I × Copies Bool m) (fun s => owner s.1)
        (conjugateKernel (copyMixerKernel m U) (copiesKernel m rho)) =
      f (I × Copies Bool m) (fun s => owner s.1) (copiesKernel m rho)) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] (e : I ≃ J)
    (owner : J → Fin 2) (rho : OscillatorKernel I), InDomain cap rho →
    InDomain cap (fun u v => rho (u ∘ e) (v ∘ e)) →
    f J owner (fun u v => rho (u ∘ e) (v ∘ e)) = f I (owner ∘ e) rho)

/-- **Hypothesis 3 of the extremality theorem: strong super-additivity**, arXiv:quant-ph/0608032v1,
p.2: "3. strong super-additivity: f(ρ_{A1...N B1...N}) ≥ f(ρ_{A1B1}) + ... + f(ρ_{ANBN}) with
equality if ρ_{A1...N B1...N} = ρ_{A1B1} ⊗ ... ⊗ ρ_{ANBN}", in its `N = 2` instance.

For every finite mode set `A` with owner map `a` (one block `A_k B_k`), and the doubled system
`A ⊕ A` with owner `Sum.elim a a`:
(1) `f(ρ_1) + f(ρ_2) ≤ f(ρ)` for every state `ρ` of the two blocks with block marginals
`ρ_1, ρ_2`;
(2) `f(ρ_1 ⊗ ρ_2) = f(ρ_1) + f(ρ_2)` for all states `ρ_1, ρ_2` of one block,
whenever the states involved lie in `InDomain cap`.

**Formalization Note** Unlike Support50.P14 `StronglySuperadditive`, the two blocks are copies
of the same system, as in the paper. The paper's hypothesis for every `N` implies this `N = 2`
form. -/
def CopySuperadditive (cap : Option ℝ) (f : MultipartiteOscillatorFunctional 2) : Prop :=
  (∀ (A : Type) [Fintype A] (a : A → Fin 2) (rho : OscillatorKernel (A ⊕ A)),
    InDomain cap rho → InDomain cap (marginalFirst rho) → InDomain cap (marginalSecond rho) →
    f A a (marginalFirst rho) + f A a (marginalSecond rho) ≤ f (A ⊕ A) (Sum.elim a a) rho) ∧
  (∀ (A : Type) [Fintype A] (a : A → Fin 2) (rho sigma : OscillatorKernel A),
    InDomain cap rho → InDomain cap sigma → InDomain cap (oscillatorTensor rho sigma) →
    f (A ⊕ A) (Sum.elim a a) (oscillatorTensor rho sigma) = f A a rho + f A a sigma)

end GaussOptCVQKD


