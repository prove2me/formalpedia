-- Prove2me | Definitions.Def_SquashedKey_Information
-- name    : SquashedKey_Information
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:55.958399+00:00
-- url     : https://prove2.me/theorems/1a6c7b2f-902b-4ebf-9495-34cde2bf3191
-- title:
--   Conditional mutual information $I(X;Y|Z)$ in bits (Shirokov's extension) and squashed entanglement $E_{sq}$
-- statement:
--   **Conditional mutual information ((15), p.5).** For a state $\rho_{XYZ}$,
--   $$
--   I(X;Y|Z)_\rho=H(XZ)_\rho+H(YZ)_\rho-H(Z)_\rho-H(XYZ)_\rho ,
--   $$
--   in bits. When the systems are infinite-dimensional the four entropies can be infinite, and the quantity used is Shirokov's extension: the supremum, over finite-rank projectors $P$ on $X$, of $I(PX;YZ)-I(PX;Z)$ (computed on the normalized compressed states, homogeneously extended). It coincides with (15) whenever the entropies in (15) are finite and takes values in $[0,+\infty]$.
--
--   **Marginals and regrouping.** For a multipartite state and a choice of which registers form $X$, $Y$, $Z$ and which are discarded, $I(X;Y|Z)$ of the corresponding marginal is computed after relabelling the registers and tracing out the discarded ones.
--
--   **Squashed entanglement ((28), p.7).** For a bipartite state $\rho_{XY}$,
--   $$
--   E_{sq}(X;Y)_\rho=\frac12\inf_{\omega_{XYE}}\bigl\{I(X;Y|E)_\omega:\ \rho_{XY}=\operatorname{Tr}_E\omega_{XYE}\bigr\},
--   $$
--   the infimum over all extensions $\omega_{XYE}$ of $\rho_{XY}$, on every extending system $E$ of any dimension.
--
--   These are the information quantities of Lemma 1, (32)–(33), (21) and Theorem 2.
--
--   **Formalization Note** Hilbert spaces are $\ell^2$ of arbitrary index types and operators are coefficient arrays (published bundle `Dependency50_P33`). The extended conditional mutual information is the published `qcmi` of `Renew46_P08` (nats, register order $X\times(Y\times Z)$ with the conditioning system last), reassociated from $(X\times Y)\times Z$ and divided by $\ln 2$. Partial traces are `partialTraceSecond` of `Frontier18_P08`. $E_{sq}$ is an infimum in $[0,+\infty]$ over every type $E$ and every state on $(X\times Y)\times E$ whose partial trace over $E$ is $\rho$; the set is nonempty ($E$ a one-point type).
-- source:
--   Wilde, Squashed entanglement and approximate private states, arXiv:1606.08028v3, §2.4 (15), p.5; §2.5 (28), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceSecond)
open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

namespace SquashedKey

/-- **Conditional quantum mutual information `I(X; Y|Z)` in bits**, Wilde, *Squashed entanglement
and approximate private states*, arXiv:1606.08028v3, §2.4, (15), p.5 (PDF p.5):
`I(A; B|E)_ρ ≡ H(AE)_ρ + H(BE)_ρ − H(E)_ρ − H(ABE)_ρ`, with `H` the entropy in bits. The argument
is the coefficient array of a tripartite operator with registers grouped `(X × Y) × Z`, where `Z` is
the conditioning system.

**Formalization Note** Formula (15) is `∞ − ∞` as soon as the entropies are infinite, which happens
for the infinite-dimensional shields and extensions the paper allows. The quantity used is
Shirokov's extended conditional mutual information `qcmi` (published bundle
`QAlgorithms_Papers_Independent_Renew46_P08`, arXiv:1512.09047), the supremum over finite-rank
projectors `P` on `X` of `I(PX; YZ) − I(PX; Z)`. It equals (15) whenever the entropies in (15) are
finite, and it is the quantity for which the continuity bound (21) of [Shi17] is proved. `qcmi` is
in nats and takes the register order `X × (Y × Z)` with the conditioning system last, so the array is
first reassociated by `Equiv.prodAssoc` and the result divided by `ln 2`. The value lies in
`ℝ≥0∞` (it can be `+∞`). -/
noncomputable def cmiBits {X Y Z : Type} (ρ : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) : ℝ≥0∞ :=
  qcmi (Matrix.reindex (Equiv.prodAssoc X Y Z) (Equiv.prodAssoc X Y Z) ρ) /
    ENNReal.ofReal (Real.log 2)

/-- **Conditional mutual information of a regrouped marginal**, arXiv:1606.08028v3, §2.4, (15), p.5,
as used in Lemma 1 and (32)–(51), pp.7–9. For a multipartite operator on index type `I` and a
relabelling `e : I ≃ ((X × Y) × Z) × D` of its registers, this is `I(X; Y|Z)` of the marginal
obtained by tracing out the discarded registers `D`.

**Formalization Note** Systems are coordinates of a product index type, so grouping several
registers into one system (e.g. `BB′`) and reordering them is a relabelling of indices by an
equivalence (`Matrix.reindex`); the partial trace `Tr_D` is `partialTraceSecond` of the published
bundle `Frontier18_P08`. When nothing is traced out, `D = Unit`. -/
noncomputable def cmiOf {I X Y Z D : Type} (e : I ≃ ((X × Y) × Z) × D) (ρ : Matrix I I ℂ) :
    ℝ≥0∞ :=
  cmiBits (partialTraceSecond (Matrix.reindex e e ρ))

/-- **Squashed entanglement**, arXiv:1606.08028v3, §2.5, (28), p.7 (PDF p.7):
`E_sq(A; B)_ρ ≡ ½ inf_{ω_ABE} {I(A; B|E)_ω : ρ_AB = Tr_E{ω_ABE}}`, "where the infimum is with
respect to all extensions `ω_ABE` of the state `ρ_AB`".

**Formalization Note** The infimum ranges over every extension system `E : Type` (finite or
infinite, with no countability or finiteness condition) and every state `ω` on `(X × Y) × E` whose
partial trace over `E` is `ρ`. The set is nonempty (`E = Unit`, `ω = ρ ⊗ |()⟩⟨()|`). `I` is the
extended conditional mutual information in bits (`cmiBits`), so the value lies in `ℝ≥0∞`. -/
noncomputable def squashedEntanglement {X Y : Type} (ρ : State (X × Y)) : ℝ≥0∞ :=
  ⨅ (E : Type) (ω : State ((X × Y) × E))
    (_ : partialTraceSecond ω.coefficients = ρ.coefficients), cmiBits ω.coefficients / 2

end SquashedKey


