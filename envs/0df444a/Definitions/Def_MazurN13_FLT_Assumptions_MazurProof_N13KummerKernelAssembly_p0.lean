-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13KummerKernelAssembly_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13KummerKernelAssembly_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:54:47.565579+00:00
-- url     : https://prove2.me/theorems/9e79b125-f990-4fb3-99fe-d6a3c37540d9
-- title:
--   FLT.Assumptions.MazurProof.N13KummerKernelAssembly source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13KummerKernelAssembly

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13KummerKernelAssembly
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityHalf_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicEndgame_p0

set_option autoImplicit false




/-!
# Removing the even-sextic infinity ambiguity from the N13 Kummer kernel

The generic fake-Kummer kernel theorem for an even sextic has two branches:
a class is either a double, or a double plus the difference of the two
points at infinity.  For N13 the latter class is itself a double, by the
explicit half-class constructed in `N13InfinityHalf`.

This file records the exact group-theoretic assembly.  Its only remaining
input is the genuine generic Kummer-kernel theorem; no finiteness or
representative enumeration occurs here.
-/

namespace MazurProof.N13KummerKernelAssembly

noncomputable section

abbrev M :=
  N13Mumford.model ℚ

abbrev O :=
  N13Infinity.positiveInfinityOrder ℚ

abbrev G : Type :=
  SexticMumford.ConcretePic M O

def infinityClass : G :=
  SexticMumford.classOf M O
    (SexticMumford.infinityMinusMumford M)

def infinityHalfClass : G :=
  SexticMumford.classOf M O N13InfinityHalf.infinityHalf

theorem two_nsmul_infinityHalfClass :
    2 • infinityHalfClass = infinityClass := by
  exact N13InfinityHalf.two_nsmul_classOf_infinityHalf

/-- Once the generic kernel has the standard two even-sextic branches,
the explicit N13 half-class turns it into exactly the subgroup of doubles. -/
theorem kernel_eq_doubles
    {T : Type*} [AddCommGroup T]
    (kummer : G →+ T)
    (kernel_double_or_infinity :
      ∀ P : G, kummer P = 0 ↔
        (∃ Q : G, P = 2 • Q) ∨
        (∃ Q : G, P = 2 • Q + infinityClass)) :
    ∀ P : G, kummer P = 0 ↔ ∃ Q : G, P = 2 • Q := by
  intro P
  constructor
  · intro hP
    rcases (kernel_double_or_infinity P).mp hP with hdouble | hinfinity
    · exact hdouble
    · obtain ⟨Q, hQ⟩ := hinfinity
      refine ⟨Q + infinityHalfClass, ?_⟩
      rw [nsmul_add, two_nsmul_infinityHalfClass]
      exact hQ
  · rintro ⟨Q, rfl⟩
    exact (kernel_double_or_infinity (2 • Q)).mpr
      (Or.inl ⟨Q, rfl⟩)

/-- Triviality of the assembled Kummer map is precisely the doubling
surjectivity required by the two-adic endgame. -/
theorem twoSurjective_of_kummer_trivial
    {T : Type*} [AddCommGroup T]
    (kummer : G →+ T)
    (kernel_double_or_infinity :
      ∀ P : G, kummer P = 0 ↔
        (∃ Q : G, P = 2 • Q) ∨
        (∃ Q : G, P = 2 • Q + infinityClass))
    (kummer_trivial : ∀ P : G, kummer P = 0) :
    N13TwoAdicEndgame.TwoSurjective G := by
  intro P
  exact
    (kernel_eq_doubles kummer kernel_double_or_infinity P).mp
      (kummer_trivial P)

end

end MazurProof.N13KummerKernelAssembly


