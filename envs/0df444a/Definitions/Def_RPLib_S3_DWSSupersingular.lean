-- Prove2me | Definitions.Def_RPLib_S3_DWSSupersingular
-- name    : RPLib_S3_DWSSupersingular
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:33:53.399882+00:00
-- url     : https://prove2.me/theorems/50bdb316-aa6c-416a-97b2-7ac93a99c34c
-- title:
--   Weight-two Ramanujan-Petersson library: S3-DWS-Supersingular (umbrella)
-- statement:
--   S3-DWS-Supersingular (umbrella).
--
--   Headline results of the unit, in namespace `RamanujanPetersson.S3`:
--   * `DWSS.dwsSuper : DWSSuper`: boundedly many supersingular level-`M` pairs over `F_{p^m}` (Hasse invariant route:
--     `SS_Fib`, `SS_HasseA`, `SS_HasseB`, `SS_HasseC`, `SS_Super`).
--   * `jFibre : JFibre`: the fibres `j ∈ {0, 1728}` (`c₄ = 0 ∨ c₆ = 0`) hold at most `2 M²` level-`M` Tate pairs.
--   * `pChainSum : PChainSum` and `pChain : PChain`: the p-chain lemma for `ellCount` (lattice combinatorics,
--     `PC_A` to `PC_G`).
--   * `dwsSupersingular`: all four together.
--
--   Tate's isogeny theorem is not used (design decision D6). No axioms beyond Lean's standard ones.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_SSSuper
import Definitions.Def_RPLib_S3_PCG

/-!
# S3-DWS-Supersingular (umbrella)

Headline results of the unit, in namespace `RamanujanPetersson.S3`:
* `DWSS.dwsSuper : DWSSuper`: boundedly many supersingular level-`M` pairs over `F_{p^m}` (Hasse invariant route:
  `SS_Fib`, `SS_HasseA`, `SS_HasseB`, `SS_HasseC`, `SS_Super`).
* `jFibre : JFibre`: the fibres `j ∈ {0, 1728}` (`c₄ = 0 ∨ c₆ = 0`) hold at most `2 M²` level-`M` Tate pairs.
* `pChainSum : PChainSum` and `pChain : PChain`: the p-chain lemma for `ellCount` (lattice combinatorics,
  `PC_A` to `PC_G`).
* `dwsSupersingular`: all four together.

Tate's isogeny theorem is not used (design decision D6). No axioms beyond Lean's standard ones.
-/

set_option autoImplicit false

open WeierstrassCurve RPLib RPLib.TateNF

namespace RamanujanPetersson.S3

/-- (S3-DWS-Supersingular, D7) The `j ∈ {0, 1728}` fibres of the level-`M` Tate pairs are bounded uniformly in `m`. -/
def JFibre : Prop :=
  ∀ (M : ℕ), 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ (m : ℕ) (F : Type) [Field F] [Fintype F]
    [DecidableEq F], Fintype.card F = p ^ m →
      Nat.card {bc : F × F // bc ∈ Y1 F M ∧ ((tate bc.1 bc.2).c₄ = 0 ∨ (tate bc.1 bc.2).c₆ = 0)} ≤ 2 * M ^ 2

theorem jFibre : JFibre := by
  intro M hM p _ hpM m F _ _ _ hq
  have : CharP F p := charP_of_card_eq_prime_pow hq
  have hMF : (M : F) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff F p M).mp h)
  exact DWSS.card_jFibre_le hM hMF

/-- **S3-DWS-Supersingular.** -/
theorem dwsSupersingular : DWSSuper ∧ JFibre ∧ PChainSum ∧ PChain :=
  ⟨DWSS.dwsSuper, jFibre, pChainSum, pChain⟩

end RamanujanPetersson.S3


