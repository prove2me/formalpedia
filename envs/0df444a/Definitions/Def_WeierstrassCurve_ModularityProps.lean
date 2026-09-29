-- Prove2me | Definitions.Def_WeierstrassCurve_ModularityProps
-- name    : WeierstrassCurve_ModularityProps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/95feb844-4c0f-5378-9e54-37521bd6a3c4
-- title:
--   Modularity inputs: unipotency, 3–5 switch, residual modularity lifting
-- statement:
--   Five predicates on integral Weierstrass models are introduced, all phrased for a chosen model $W$ over $\mathbb{Z}$ rather than for an isomorphism class over $\mathbb{Q}$.
--
--   `ModRepHasUnipotent W n` asserts the existence of a $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose induced $\mathbb{Z}/n$-linear endomorphism $u = \rho(\sigma)$ of the $n$-torsion submodule of the group of affine points of $W$ base-changed to $\overline{\mathbb{Q}}$ (the endomorphism supplied by `galoisRepModuleEnd`) satisfies $(u-1)(u-1) = 0$ together with $u - 1 \neq 0$: some Galois element acts unipotently but non-trivially.
--
--   The remaining four are named statements to be cited as hypotheses: `LanglandsTunnellWeightTwo` and `ModularityLiftingAt p` are closed propositions (the latter depending only on a prime), while `ModThreeOrFiveIrreducible W` and `ThreeFiveSwitchCurve W` depend on the model $W$. `LanglandsTunnellWeightTwo` says: every $W$ with $\Delta \neq 0$ which is semistable in the project's sense (no prime dividing $\Delta$ divides $c_4$) and has irreducible mod-$3$ torsion representation is residually modular at $3$, meaning that for some level $M > 0$ there is a normalised weight-two eigenform on $\Gamma_0(M)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $3$ with $a_\ell(f) \equiv a_\ell(W) \pmod{\mathfrak{m}}$ for all primes $\ell \nmid \Delta$, $\ell \nmid M$, $\ell \neq 3$, where $a_\ell(W)$ is computed as $\ell + 1 - \#W(\mathbb{F}_\ell)$ for the reduction of the model. `ModThreeOrFiveIrreducible W` says that a semistable $W$ with $\Delta \neq 0$ has irreducible mod-$3$ or mod-$5$ torsion representation. `ThreeFiveSwitchCurve W` says that for such $W$ with irreducible mod-$5$ representation there is a second model $W'$ with $\Delta' \neq 0$, semistable, mod-$3$ irreducible, possessing a non-trivial unipotent in its mod-$3$ representation, satisfying $3 \mid \Delta'$ or $3 \nmid a_3(W')$, and congruent to $W$ in the sense that $5 \mid a_\ell(W') - a_\ell(W)$ for every prime $\ell \neq 5$ good for both. `ModularityLiftingAt p` says that semistability, $\Delta \neq 0$, mod-$p$ irreducibility and residual modularity at $p$ imply that $W$ is modular of some level $N > 0$ divisible by every prime dividing $\Delta$. A local instance equips $\overline{\mathbb{Q}}$ with classical decidable equality, as required by the torsion-representation definitions.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, `CuspForm` and the congruence subgroups $\Gamma_0(N)$, but no notion of modularity of an elliptic curve, of residual modularity, or of the mod-$n$ Galois representation on torsion; all predicates here are the project's own, built on its $\mathbb{Z}/n$-module structure on the $n$-torsion of the points over $\overline{\mathbb{Q}}$ and on Frobenius traces defined by point counts of reductions.
--
--   **Where it is used.** These predicates are the vocabulary in which modularity of semistable elliptic curves over $\mathbb{Q}$ is assembled: the argument splits according to whether the mod-$3$ representation is irreducible, using `LanglandsTunnellWeightTwo` and `ModularityLiftingAt 3` in that case, and otherwise `ModThreeOrFiveIrreducible`, `ThreeFiveSwitchCurve` and `ModularityLiftingAt 5` to transfer the conclusion from an auxiliary curve congruent mod $5$. The resulting modularity statement is what is applied to the Frey curve attached to a solution of the Fermat equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ModularityProps.lean

import Mathlib.NumberTheory.FLT.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Algebra.Basic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

noncomputable section

namespace WeierstrassCurve

open CuspForm ModularFormClass

noncomputable local instance instDecEqQbarNo2Assembly :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModRepHasUnipotent (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ - 1)
        * (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ
            - 1) = 0 ∧
      galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ
          - 1 ≠ 0

def LanglandsTunnellWeightTwo : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 3 →
    W.IsResiduallyModular 3

def ModThreeOrFiveIrreducible (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel →
    (W.ModRepIsIrreducible 3 ∨ W.ModRepIsIrreducible 5)

def ThreeFiveSwitchCurve (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 5 →
    ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧
      W'.ModRepIsIrreducible 3 ∧ W'.ModRepHasUnipotent 3 ∧
      (¬ W'.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W'.apOfModel 3) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
        (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)

def ModularityLiftingAt (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    W.IsResiduallyModular p → W.IsModularModelOfConductorLevel

end WeierstrassCurve

end


