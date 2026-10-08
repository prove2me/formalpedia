-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N18RouteC_Separated_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N18RouteC_Separated_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:46:54.080653+00:00
-- url     : https://prove2.me/theorems/1ee3b82e-63e8-4a18-9762-fc29019a7746
-- title:
--   FLT.Assumptions.MazurProof.N18RouteC_Separated source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N18RouteC_Separated

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N18RouteC_Separated
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N18RouteC_PushPull_p0

set_option autoImplicit false




/-!
# Weak descent and formal-kernel separatedness for N18 Route C

This file is independent of any Mordell--Weil finite-generation theorem.  It
turns a weak `3`-descent, a seven-torsion reduction group, and strict growth in
the formal kernel into the uniform annihilator `[21]`.
-/

namespace MazurProof.N18RouteC.Separated

noncomputable section

def InfinitelyNSmulDivisible
    {G : Type*} [AddCommGroup G] (n : ℕ) (x : G) : Prop :=
  ∀ k : ℕ, ∃ y : G, (n ^ k) • y = x

def NSeparated (G : Type*) [AddCommGroup G] (n : ℕ) : Prop :=
  ∀ x : G, InfinitelyNSmulDivisible n x → x = 0

def WeakDescentWitness
    (G : Type*) [AddCommGroup G] (n a : ℕ) : Prop :=
  ∀ x : G, ∃ h y : G, a • h = 0 ∧ x = h + n • y

theorem nsmul_nsmul_comm
    {G : Type*} [AddCommGroup G]
    (m n : ℕ) (x : G) :
    m • (n • x) = n • (m • x) := by
  calc
    m • (n • x) = (n * m) • x := (mul_nsmul x n m).symm
    _ = (m * n) • x := by rw [Nat.mul_comm]
    _ = n • (m • x) := mul_nsmul x m n

theorem nsmul_eq_zero_of_dvd
    {G : Type*} [AddCommGroup G]
    {a e : ℕ} (hae : a ∣ e) {x : G}
    (hx : a • x = 0) : e • x = 0 := by
  rcases hae with ⟨c, rfl⟩
  calc
    (a * c) • x = (c * a) • x := by rw [Nat.mul_comm]
    _ = (a * c) • x := by rw [Nat.mul_comm]
    _ = c • (a • x) := mul_nsmul x a c
    _ = 0 := by rw [hx, nsmul_zero]

theorem weakDescent_iter_commonMultiple
    {G : Type*} [AddCommGroup G]
    {n a e : ℕ}
    (weak : WeakDescentWitness G n a)
    (hae : a ∣ e) :
    ∀ k : ℕ, ∀ x : G,
      ∃ y : G, e • x = (n ^ k) • (e • y) := by
  intro k
  induction k with
  | zero =>
      intro x
      exact ⟨x, by simp⟩
  | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨h, z, hh, hz⟩ := weak y
      have heh : e • h = 0 := nsmul_eq_zero_of_dvd hae hh
      refine ⟨z, ?_⟩
      calc
        e • x = (n ^ k) • (e • y) := hy
        _ = (n ^ k) • (e • (h + n • z)) := by rw [hz]
        _ = (n ^ k) • (n • (e • z)) := by
          congr 1
          rw [nsmul_add, heh, zero_add]
          exact nsmul_nsmul_comm e n z
        _ = (n ^ (k + 1)) • (e • z) := by
          calc
            (n ^ k) • (n • (e • z)) =
                (n * n ^ k) • (e • z) :=
              (mul_nsmul (e • z) n (n ^ k)).symm
            _ = (n ^ k * n) • (e • z) := by rw [Nat.mul_comm]
            _ = (n ^ (k + 1)) • (e • z) := by rw [pow_succ]

theorem annihilated_of_commonMultiple
    {G A R : Type*}
    [AddCommGroup G] [AddCommGroup A] [AddCommGroup R]
    (loc : G →+ A)
    (hloc : Function.Injective loc)
    (red : A →+ R)
    (n a b e : ℕ)
    (weak : WeakDescentWitness G n a)
    (killRed : ∀ r : R, b • r = 0)
    (hae : a ∣ e)
    (hbe : b ∣ e)
    (separated : NSeparated red.ker n) :
    ∀ x : G, e • x = 0 := by
  have killRedE : ∀ r : R, e • r = 0 := by
    intro r
    exact nsmul_eq_zero_of_dvd hbe (killRed r)
  have hiter := weakDescent_iter_commonMultiple weak hae
  intro x
  let P : red.ker :=
    ⟨loc (e • x), by
      change red (loc (e • x)) = 0
      simpa only [map_nsmul] using killRedE (red (loc x))⟩
  have hdiv : InfinitelyNSmulDivisible n P := by
    intro k
    obtain ⟨y, hy⟩ := hiter k x
    let Q : red.ker :=
      ⟨loc (e • y), by
        change red (loc (e • y)) = 0
        simpa only [map_nsmul] using killRedE (red (loc y))⟩
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    simpa [P, Q] using congrArg loc hy.symm
  have hP0 : P = 0 := separated P hdiv
  apply hloc
  simpa [P] using congrArg Subtype.val hP0

theorem annihilated_of_weakDescent_and_separated
    {G A R : Type*}
    [AddCommGroup G] [AddCommGroup A] [AddCommGroup R]
    (loc : G →+ A)
    (hloc : Function.Injective loc)
    (red : A →+ R)
    (n a b : ℕ)
    (weak : WeakDescentWitness G n a)
    (killRed : ∀ r : R, b • r = 0)
    (separated : NSeparated red.ker n) :
    ∀ x : G, Nat.lcm a b • x = 0 := by
  exact annihilated_of_commonMultiple loc hloc red n a b (Nat.lcm a b)
    weak killRed (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b) separated

structure StrictNSmulFiltration
    (K : Type*) [AddCommGroup K] (n : ℕ) where
  level : K → ℕ
  step : ∀ {x : K},
    x ≠ 0 → n • x ≠ 0 → level x + 1 ≤ level (n • x)

theorem StrictNSmulFiltration.iterate
    {K : Type*} [AddCommGroup K]
    {n : ℕ}
    (D : StrictNSmulFiltration K n)
    {x : K} :
    ∀ k : ℕ,
      (n ^ k) • x ≠ 0 →
        D.level x + k ≤ D.level ((n ^ k) • x) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hfinal
      have hpow :
          (n ^ (k + 1)) • x = n • ((n ^ k) • x) := by
        calc
          (n ^ (k + 1)) • x = (n ^ k * n) • x := by rw [pow_succ]
          _ = (n * n ^ k) • x := by rw [Nat.mul_comm]
          _ = (n ^ k) • (n • x) := mul_nsmul x n (n ^ k)
          _ = n • ((n ^ k) • x) := nsmul_nsmul_comm (n ^ k) n x
      have hprev : (n ^ k) • x ≠ 0 := by
        intro hz
        apply hfinal
        rw [hpow, hz, nsmul_zero]
      have hstepNe : n • ((n ^ k) • x) ≠ 0 := by
        rw [← hpow]
        exact hfinal
      have hi := ih hprev
      have hs := D.step hprev hstepNe
      calc
        D.level x + (k + 1) = (D.level x + k) + 1 := by omega
        _ ≤ D.level ((n ^ k) • x) + 1 := Nat.add_le_add_right hi 1
        _ ≤ D.level (n • ((n ^ k) • x)) := hs
        _ = D.level ((n ^ (k + 1)) • x) := by
          rw [hpow]

theorem StrictNSmulFiltration.separated
    {K : Type*} [AddCommGroup K]
    {n : ℕ}
    (D : StrictNSmulFiltration K n) :
    NSeparated K n := by
  intro P hdiv
  by_contra hP
  let N : ℕ := D.level P + 1
  obtain ⟨Q, hQ⟩ := hdiv N
  have hfinal : (n ^ N) • Q ≠ 0 := by
    rw [hQ]
    exact hP
  have hi := D.iterate N hfinal
  rw [hQ] at hi
  dsimp [N] at hi
  omega

theorem e0_killed_by_21
    {E0Point LocalPoint RedPoint : Type*}
    [AddCommGroup E0Point]
    [AddCommGroup LocalPoint]
    [AddCommGroup RedPoint]
    (loc : E0Point →+ LocalPoint)
    (hloc : Function.Injective loc)
    (red : LocalPoint →+ RedPoint)
    (weakBlock4 : ∀ P : E0Point,
      ∃ h : E0Point, 3 • h = 0 ∧
        ∃ Q : E0Point, P = h + 3 • Q)
    (reductionExponentSeven : ∀ r : RedPoint, 7 • r = 0)
    (formalFiltration : StrictNSmulFiltration red.ker 3) :
    ∀ P : E0Point, 21 • P = 0 := by
  have weak : WeakDescentWitness E0Point 3 3 := by
    intro P
    obtain ⟨h, hh, Q, hPQ⟩ := weakBlock4 P
    exact ⟨h, Q, hh, hPQ⟩
  have h := annihilated_of_weakDescent_and_separated
    loc hloc red 3 3 7 weak reductionExponentSeven
      formalFiltration.separated
  intro P
  simpa [show Nat.lcm 3 7 = 21 by decide] using h P

theorem annihilator_transfer_injective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B)
    (hf : Function.Injective f)
    (m : ℕ)
    (killB : ∀ b : B, m • b = 0) :
    ∀ a : A, m • a = 0 := by
  intro a
  apply hf
  simpa only [map_nsmul, map_zero] using killB (f a)

theorem pushPull_annihilator
    {J A B : Type*}
    [AddCommGroup J] [AddCommGroup A] [AddCommGroup B]
    (Phi : J →+ A × B)
    (Psi : A × B →+ J)
    (m : ℕ)
    (killA : ∀ a : A, m • a = 0)
    (killB : ∀ b : B, m • b = 0)
    (pushPull : ∀ D : J, Psi (Phi D) = 2 • D) :
    ∀ D : J, (2 * m) • D = 0 := by
  intro D
  have hpair : m • Phi D = 0 := by
    apply Prod.ext
    · simpa using killA (Phi D).1
    · simpa using killB (Phi D).2
  calc
    (2 * m) • D = m • (2 • D) := by
      calc
        (2 * m) • D = (m * 2) • D := by rw [Nat.mul_comm]
        _ = (2 * m) • D := by rw [Nat.mul_comm]
        _ = m • (2 • D) := mul_nsmul D 2 m
    _ = m • Psi (Phi D) := by rw [← pushPull D]
    _ = Psi (m • Phi D) := by rw [map_nsmul]
    _ = 0 := by rw [hpair, map_zero]

end

end MazurProof.N18RouteC.Separated


