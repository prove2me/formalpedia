-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
-- name    : OAI_GroupTheory_Kervaire_Reductions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:00:32.623995+00:00
-- url     : https://prove2.me/theorems/0f79210c-8eb8-4444-9321-0677febfe027
-- title:
--   The exponent sum modulo itself and the cyclic quotient
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Exponent residue.** For $w\in A*\langle t\rangle$ with exponent sum $e(w)$, the homomorphism $A*\langle t\rangle\to\mathbb Z/|e(w)|$ that kills $A$ and sends $t$ to $1$. It sends $w$ to $0$.
--   2. **Cyclic quotient map.** The induced surjection
--   $$
--   (A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle\ \longrightarrow\ \mathbb Z/|e(w)|,\qquad t\mapsto1 .
--   $$
--   So the one-relator quotient always maps onto the expected cyclic group, and the unimodular case $|e(w)|=1$ is the one where this gives no information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Reductions.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Reductions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire

namespace OAI

namespace Kervaire

universe u

def exponentMod {A : Type u} [Group A] (w : WordGroup A) :
    WordGroup A →* Multiplicative (ZMod (exponentSum w).natAbs) :=
  (Int.castAddHom (ZMod (exponentSum w).natAbs)).toMultiplicative.comp Monoid.Coprod.snd

@[simp] theorem exponentMod_relator {A : Type u} [Group A] (w : WordGroup A) :
    exponentMod w w = 1 := by
  change ((exponentSum w : ℤ) : ZMod (exponentSum w).natAbs) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natAbs_dvd.mpr (dvd_refl _))

/-- The quotient always surjects onto the expected cyclic exponent quotient. -/
def cyclicQuotientMap {A : Type u} [Group A] (w : WordGroup A) :
    RelatorQuotient w →* Multiplicative (ZMod (exponentSum w).natAbs) :=
  QuotientGroup.lift (relatorClosure w) (exponentMod w) (by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    have hxw : x = w := Set.mem_singleton_iff.mp hx
    subst x
    exact exponentMod_relator w)

@[simp] theorem cyclicQuotientMap_generator {A : Type u} [Group A] (w : WordGroup A) :
    cyclicQuotientMap w (QuotientGroup.mk (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)))) =
      Multiplicative.ofAdd (1 : ZMod (exponentSum w).natAbs) := by
  change exponentMod w (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) = _
  simp [exponentMod]

end Kervaire

end OAI


