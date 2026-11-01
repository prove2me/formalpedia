-- Prove2me | Definitions.Def_GaussOptCVQKD_KeyRate
-- name    : GaussOptCVQKD_KeyRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:19.633172+00:00
-- url     : https://prove2.me/theorems/b37eb93d-b3cc-4b59-80c2-b2eb9cf73b71
-- title:
--   The conditional states $\rho^a_B$, the Holevo term $\int p(a)S(\rho^a_B)\,da$ and the key rate $K_\beta(\rho_{AB})$ (DR and RR)
-- statement:
--   **Conditional states ((1), p.1).** After party $p$ measures and obtains $a$ (law $\nu$), the other party's modes are in the state $\rho^a$; the classical–quantum state is $\int d\nu(a)\,|a\rangle\langle a|\otimes\rho^a$. The family $(\nu,\rho^a)$ is characterized by: each $\rho^a$ is a density, and for all frequencies $\eta$ and Weyl arguments $\xi$ of the other party's modes,
--   $$
--   \int e^{i\eta\cdot a}\operatorname{Tr}\bigl(\rho^a W(\xi)\bigr)\,d\nu(a)=\operatorname{Tr}\bigl(\rho\,(F(\eta)\otimes W(\xi))\bigr),
--   $$
--   where $F(\eta)=\int e^{i\eta\cdot a}\,dE(a)$ is the characteristic operator of party $p$'s measurement (a Weyl operator on the measured quadratures, times $e^{-|\eta|^2/4}$ for heterodyne).
--
--   **Holevo term (p.2).** $\int d\nu(a)\,S(\rho^a)$, with $S$ the von Neumann entropy in nats; Eve's Holevo information about Alice's outcome is
--   $$
--   \chi_{aE}=S(\rho_{AB})-\int da\,p(a)\,S(\rho^a_B).
--   $$
--
--   **Key rate ((6), (7), (11), pp.3–4).** For $\beta\in[0,1]$,
--   $$
--   K_\beta(\rho_{AB})=\beta\,S(a{:}b)-\chi_{aE}\quad\text{(direct reconciliation)},\qquad K_\beta(\rho_{AB})=\beta\,S(a{:}b)-\chi_{bE}\quad\text{(reverse reconciliation)},
--   $$
--   with $\chi_{bE}=S(\rho_{AB})-\int db\,p(b)S(\rho^b_A)$ ("interchange $a\leftrightarrow b$ and $A\leftrightarrow B$", p.3). $\beta=1$ with DR is (6) for one mode per party and (7) for $N$ modes per party.
--
--   **Formalization Note** $K$ is a functional of every finite mode set with every owner map (Support50.P14 `MultipartiteOscillatorFunctional 2`). The conditional-entropy integral is an infimum over all families satisfying the relation (they agree $\nu$-almost everywhere); with no such family it is $+\infty$. $S(\rho)$ is the published `extendedEntropyNats`. The three pieces are in $[0,\infty]$ and are converted to reals in $K$; every theorem of the mission that uses $K$ concludes or assumes that they are finite.
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, (1) p.1, Holevo bound p.2, (6)–(7) p.3, RR p.3, (11) p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_GaussOptCVQKD_MeasurementModel

open MeasureTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel InterleavedQuadrature oscillatorCharacteristic MultipartiteOscillatorFunctional)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace GaussOptCVQKD

/-- The Weyl argument on all modes that puts the frequency vector `η` of party `p`'s outcome on
`p`'s measured coordinates and the Weyl argument `ξq` on the modes owned by party `q`. -/
noncomputable def assemble {I : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (p q : Fin 2) (η : PartyOutcome owner choice p)
    (ξq : InterleavedQuadrature {j : I // owner j = q} → ℝ) : InterleavedQuadrature I → ℝ :=
  fun r => if h : owner r.1 = q then ξq (⟨r.1, h⟩, r.2) else embedOutcome owner choice p η r

/-- **Conditional states `ρ^a_B` after party `p`'s measurement**, García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, (1), p.1: `ρ_aB = ∫ da p(a) |a⟩⟨a| ⊗ ρ^a_B`.

`ν` is the law `p(a)` of party `p`'s outcome and `c a` the state `ρ^a` of party `q`'s modes
given outcome `a`: every `c a` is a density, and the classical–quantum state `∫ ν(da) δ_a ⊗ c a`
has the Born-rule joint characteristic function,
`∫ exp(i η·a) Tr(c a · W(ξq)) dν(a) = Tr(ρ (F(η) ⊗ W(ξq)))`, with `F(η) = ∫ exp(i η·a) dE(a)` the
characteristic operator of party `p`'s measurement (a Weyl operator on the measured quadratures,
times the vacuum factor for heterodyne). Direct reconciliation uses `p = 0` (Alice), `q = 1`
(Bob); reverse reconciliation `p = 1`, `q = 0`.

**Formalization Note** These relations determine `ν`, and `c` up to a `ν`-null set; they are
stated through characteristic functions, so no pointwise Born series is used. -/
def IsConditionalFamily {I : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (ρ : OscillatorKernel I) (p q : Fin 2)
    (ν : Measure (PartyOutcome owner choice p))
    (c : PartyOutcome owner choice p → OscillatorKernel {j : I // owner j = q}) : Prop :=
  IsProbabilityMeasure ν ∧ (∀ a, IsDensity (c a)) ∧
    (∀ ξq : InterleavedQuadrature {j : I // owner j = q} → ℝ,
      Integrable (fun a => oscillatorCharacteristic (c a) ξq) ν) ∧
    ∀ (η : PartyOutcome owner choice p) (ξq : InterleavedQuadrature {j : I // owner j = q} → ℝ),
      ∫ a, Complex.exp (Complex.I * (pairing η a : ℂ)) * oscillatorCharacteristic (c a) ξq ∂ν =
        oscillatorCharacteristic ρ (assemble owner choice p q η ξq) *
          (heterodyneFactor choice p η : ℂ)

/-- **The averaged conditional entropy `∫ da p(a) S(ρ^a_B)`**, arXiv:quant-ph/0608032v1, p.2,
the term subtracted in `χ_aE = S(ρ_AB) − ∫ da p(a) S(ρ^a_B)`; entropies in nats, valued in
`[0, ∞]`.

**Formalization Note** An infimum over all families satisfying `IsConditionalFamily` (they agree
`ν`-almost everywhere, so the integral does not depend on the choice). If no family satisfies it
the value is `⊤`, never a junk `0`. -/
noncomputable def holevoIntegral {I : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (ρ : OscillatorKernel I) (p q : Fin 2) : ℝ≥0∞ :=
  ⨅ (ν : Measure (PartyOutcome owner choice p))
    (c : PartyOutcome owner choice p → OscillatorKernel {j : I // owner j = q})
    (_ : IsConditionalFamily owner choice ρ p q ν c),
    ∫⁻ a, extendedEntropyNats (c a) ∂ν

/-- The party whose outcome is the key: Alice (`0`) for DR, Bob (`1`) for RR. -/
def Reconciliation.keyParty : Reconciliation → Fin 2
  | .direct => 0
  | .reverse => 1

/-- The party that corrects its data: Bob (`1`) for DR, Alice (`0`) for RR. -/
def Reconciliation.otherParty : Reconciliation → Fin 2
  | .direct => 1
  | .reverse => 0

/-- **The collective-attack secret key rate `K(ρ_AB)`**, arXiv:quant-ph/0608032v1, (6) and (7),
p.3, with the reconciliation efficiency `β` of (11), p.4, and the RR variant of p.3:

`K_β = β S(a:b) − S(a:E)` (DR), `K_β = β S(a:b) − S(b:E)` (RR), where
`S(a:E) = χ_aE = S(ρ_AB) − ∫ da p(a) S(ρ^a_B)` (p.2) and, for RR, `a ↔ b`, `A ↔ B`.

`keyRate β r mA mB` is a functional of every finite mode set `I` with an owner map
`owner : I → Fin 2` (`0` = Alice, `1` = Bob) and every coefficient array `ρ` on the oscillator
Fock space of `I`; Alice measures `mA` on all her modes and Bob `mB` on all his.

**Formalization Note** `S(a:b)` is `mutualInfo` and `S(ρ_AB)` is the published
`extendedEntropyNats` (both in nats, valued in `[0, ∞]`); the three pieces are converted to reals
with `toReal`, so `K` is the paper's number only where they are finite. Every statement of the
mission that uses `K` either concludes or assumes that finiteness. Values on arrays that are not
densities are never used. -/
noncomputable def keyRate (β : ℝ) (r : Reconciliation) (mA mB : Measurement) :
    MultipartiteOscillatorFunctional 2 :=
  fun (I : Type) [Fintype I] (owner : I → Fin 2) (ρ : OscillatorKernel I) =>
    β * (mutualInfo owner ![mA, mB] ρ).toReal -
      ((extendedEntropyNats ρ).toReal -
        (holevoIntegral owner ![mA, mB] ρ r.keyParty r.otherParty).toReal)

end GaussOptCVQKD


