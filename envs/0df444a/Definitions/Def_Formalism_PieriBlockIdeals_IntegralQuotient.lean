-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_IntegralQuotient
-- name    : Formalism_PieriBlockIdeals_IntegralQuotient
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:54.960172+00:00
-- url     : https://prove2.me/theorems/277d0f30-f31c-46af-9b29-8f435bb012a5
-- title:
--   Integral Quotient
-- statement:
--   Definitions and structural lemmas for Integral Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/IntegralQuotient.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace Formalism.CohomologicalDescent.Symmetrization
abbrev Tens (R P M : Type*) (n : ℕ) := (Fin n → R × P) → M
section Ops
variable (k : Type*) {R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}
def perm (σ : Equiv.Perm (Fin n)) : Module.End k (Tens R P M n) :=
  LinearMap.funLeft k M fun g => g ∘ σ
def permY (σ : Equiv.Perm (Fin n)) : Module.End k (Tens R P M n) :=
  LinearMap.funLeft k M fun g s => ((g (σ s)).1, (g s).2)
def permX (σ : Equiv.Perm (Fin n)) : Module.End k (Tens R P M n) :=
  LinearMap.funLeft k M fun g s => ((g s).1, (g (σ s)).2)
def contr (j : Fin (n + 1)) (v : R × P) : Tens R P M (n + 1) →ₗ[k] Tens R P M n :=
  LinearMap.funLeft k M fun g => j.insertNth v g
def onM (T : Module.End k M) : Module.End k (Tens R P M n) := T.compLeft _
variable [DecidableEq R] [DecidableEq P]
def unitY (j : Fin n) (a b : R) : Module.End k (Tens R P M n) :=
  LinearMap.pi fun g => if (g j).1 = a then LinearMap.proj (Function.update g j (b, (g j).2)) else 0
def unitX (j : Fin n) (α β : P) : Module.End k (Tens R P M n) :=
  LinearMap.pi fun g => if (g j).2 = α then LinearMap.proj (Function.update g j ((g j).1, β)) else 0
variable [Fintype R]
def Om (EM : R → R → Module.End k M) (j : Fin n) : Module.End k (Tens R P M n) :=
  ∑ b, ∑ b', unitY k j b b' * onM k (EM b' b)
def xJM (EM : R → R → Module.End k M) (j : Fin n) : Module.End k (Tens R P M n) :=
  Om k EM j + ∑ j' ∈ Finset.univ.filter (· < j), permY k (Equiv.swap j' j)
def AA (EM : R → R → Module.End k M) (n : ℕ) (t : k) : Module.End k (Tens R P M n) :=
  (List.ofFn fun j : Fin n => t • (1 : Module.End k (Tens R P M n)) - xJM k EM j).prod
noncomputable def AApoly (EM : R → R → Module.End k M) (n : ℕ) : (Module.End k (Tens R P M n))[X] :=
  (List.ofFn fun j : Fin n => (X - C (xJM k EM j) : (Module.End k (Tens R P M n))[X])).prod
def diagY (EM : R → R → Module.End k M) (c d : R) : Module.End k (Tens R P M n) :=
  onM k (EM c d) + ∑ j, unitY k j c d
def diagX (w : k) (α β : P) : Module.End k (Tens R P M n) :=
  (if α = β then w • (1 : Module.End k (Tens R P M n)) else 0) - ∑ j, unitX k j β α
def GlRel {A : Type*} [Ring A] (T : R → R → A) : Prop :=
  ∀ a b c d, T a b * T c d - T c d * T a b = (if b = c then T a d else 0) - (if d = a then T c b else 0)
end Ops
section SymPow
variable (k : Type*) {ι M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}
def cont (g : Fin n → ι) : Sym ι n := ⟨Finset.univ.val.map g, by simp⟩
variable [Fintype ι] [DecidableEq ι]
def mfact (m : Sym ι n) : ℕ := ∏ v, (Multiset.count v m.1).factorial
def toSym : ((Fin n → ι) → M) →ₗ[k] (Sym ι n → M) :=
  LinearMap.pi fun m => ∑ g ∈ Finset.univ.filter (fun g : Fin n → ι => cont g = m), LinearMap.proj g
def NmS : (Sym ι n → M) →ₗ[k] ((Fin n → ι) → M) :=
  LinearMap.pi fun g => (mfact (cont g) : k) • LinearMap.proj (cont g)
end SymPow
structure HidaSetting (k V P R : Type*) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] where

  E : P ⊕ R → P ⊕ R → Module.End k V

  comm : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

  W : Submodule k V

  w : k

  kill : ∀ (α : P) (a : R), ∀ u ∈ W, E (Sum.inl α) (Sum.inr a) u = 0

  scal : ∀ (α β : P), ∀ u ∈ W, E (Sum.inl α) (Sum.inl β) u = if α = β then w • u else 0

  stab : ∀ (b b' : R), ∀ u ∈ W, E (Sum.inr b) (Sum.inr b') u ∈ W
namespace HidaSetting
variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  (S : HidaSetting k V P R)
def f (v : R × P) : Module.End k V := S.E (Sum.inr v.1) (Sum.inl v.2)
def e (v : R × P) : Module.End k V := S.E (Sum.inl v.2) (Sum.inr v.1)
def EW (b b' : R) : Module.End k S.W := (S.E (Sum.inr b) (Sum.inr b')).restrict (S.stab b b')
def Fw {n : ℕ} (g : Fin n → R × P) : Module.End k V := (List.ofFn fun s => S.f (g s)).prod
def Ew {n : ℕ} (g : Fin n → R × P) : Module.End k V := (List.ofFn fun s => S.e (g s)).prod
noncomputable def Fs {n : ℕ} (m : Sym (R × P) n) : Module.End k V := (m.1.toList.map S.f).prod
noncomputable def Es {n : ℕ} (m : Sym (R × P) n) : Module.End k V := (m.1.toList.map S.e).prod
variable [Fintype P] [Fintype R]
def mu (n : ℕ) : Tens R P S.W n →ₗ[k] V := ∑ g, S.Fw g ∘ₗ S.W.subtype ∘ₗ LinearMap.proj g
end HidaSetting
namespace HidaSetting
variable {k V P R : Type*} [Field k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  [Fintype P] [Fintype R] (S : HidaSetting k V P R)
noncomputable def act (n : ℕ) (y : Sym (R × P) n → S.W) : V := ((n.factorial : k)⁻¹) • S.mu n (NmS k y)
noncomputable def iota (n : ℕ) (v : V) : Sym (R × P) n → V := fun m => ((mfact m : k)⁻¹) • S.Es m v
end HidaSetting
def UnitYSingle : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] (n : ℕ) (j : Fin n)
    (a b : R) (g : Fin n → R × P) (u : M),
    unitY k j a b (Pi.single g u : Tens R P M n) =
      if (g j).1 = b then Pi.single (Function.update g j (a, (g j).2)) u else 0
def FlipSpec : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R] (n : ℕ)
    (i j : Fin n), i ≠ j →
    ∑ b, ∑ b', unitY k i b b' * unitY k j b' b = (permY k (Equiv.swap i j) : Module.End k (Tens R P M n))
def PermSpec : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
    (perm k σ : Module.End k (Tens R P M n)) = permY k σ * permX k σ ∧
      (perm k (σ * τ) : Module.End k (Tens R P M n)) = perm k σ * perm k τ ∧
      (permY k (σ * τ) : Module.End k (Tens R P M n)) = permY k σ * permY k τ
def MuEquivariant : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n),
    (∀ c d : R, S.E (Sum.inr c) (Sum.inr d) (S.mu n z) = S.mu n (diagY k S.EW c d z)) ∧
      (∀ α β : P, S.E (Sum.inl α) (Sum.inl β) (S.mu n z) = S.mu n (diagX k S.w α β z)) ∧
      ∀ σ : Equiv.Perm (Fin n), S.mu n (perm k σ z) = S.mu n z
def WordSpec : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) (n : ℕ) (g : Fin n → R × P), S.Fs (cont g) = S.Fw g ∧ S.Es (cont g) = S.Ew g
def AARankTwo : Prop :=
  ∀ (k M : Type) [CommRing k] [AddCommGroup M] [Module k M] (n : ℕ) (y t : k),
    (AA k (fun _ _ : Unit => y • (1 : Module.End k M)) n t : Module.End k (Tens Unit Unit M n)) =
      (∏ j ∈ Finset.range n, (t - y - (j : k))) • 1
def OneStep : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)),
    S.e v (S.mu (n + 1) z) =
      S.mu n (∑ j, contr k j v (S.w • z - Om k S.EW j z) -
        ∑ j, ∑ l ∈ Finset.univ.filter (j < ·),
          (contr k j v (permY k (Equiv.swap j l) z) + contr k l v (permY k (Equiv.swap j l) z)))
def OneStepInv : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)), (∀ σ, perm k σ z = z) →
    S.e v (S.mu (n + 1) z) =
      (n + 1) • S.mu n (contr k (Fin.last n) v (S.w • z - xJM k S.EW (Fin.last n) z))
def JMCommAbstract : Prop :=
  ∀ (A R : Type) [Ring A] [Fintype R] [DecidableEq R] (ε : ℕ → R → R → A), (∀ j, GlRel (ε j)) →
    (∀ i j, i ≠ j → ∀ a b c d, Commute (ε i a b) (ε j c d)) →
    (∀ i j, Commute (∑ a ∈ Finset.range i, ∑ b, ∑ b', ε a b b' * ε i b' b)
      (∑ a ∈ Finset.range j, ∑ b, ∑ b', ε a b b' * ε j b' b)) ∧
    ∀ j m c d, j < m → Commute (∑ a ∈ Finset.range j, ∑ b, ∑ b', ε a b b' * ε j b' b) (∑ i ∈ Finset.range m, ε i c d)
def XComm : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End k M), GlRel EM → ∀ (n : ℕ) (i j : Fin n),
    Commute (xJM k EM i : Module.End k (Tens R P M n)) (xJM k EM j)
def HeckeRel : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End k M) (n : ℕ) (j : Fin n) (hj : j.val + 1 < n),
    (permY k (Equiv.swap j ⟨j.val + 1, hj⟩) * xJM k EM j : Module.End k (Tens R P M n)) =
        xJM k EM ⟨j.val + 1, hj⟩ * permY k (Equiv.swap j ⟨j.val + 1, hj⟩) - 1 ∧
      ∀ l : Fin n, l ≠ j → l ≠ ⟨j.val + 1, hj⟩ →
        Commute (permY k (Equiv.swap j ⟨j.val + 1, hj⟩) : Module.End k (Tens R P M n)) (xJM k EM l)
def SymCommAbstract : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (x : Fin n → A) (s : A) (j : Fin n) (hj : j.val + 1 < n),
    (∀ a b, Commute (x a) (x b)) → s * s = 1 → s * x j = x ⟨j.val + 1, hj⟩ * s - 1 →
    (∀ l : Fin n, l ≠ j → l ≠ ⟨j.val + 1, hj⟩ → Commute s (x l)) →
    Commute (C s) (List.ofFn fun a => (X - C (x a) : A[X])).prod
def AAComm : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End k M), GlRel EM → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    Commute (C (permY k σ)) (AApoly k EM n : (Module.End k (Tens R P M n))[X]) ∧
      Commute (C (perm k σ)) (AApoly k EM n : (Module.End k (Tens R P M n))[X]) ∧
      ∀ t : k, Commute (permY k σ) (AA k EM n t : Module.End k (Tens R P M n)) ∧
        Commute (perm k σ) (AA k EM n t : Module.End k (Tens R P M n))
def XCommLevi : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End k M), GlRel EM → ∀ (n : ℕ) (j : Fin n),
    (∀ c d : R, Commute (xJM k EM j : Module.End k (Tens R P M n)) (diagY k EM c d)) ∧
      ∀ (w : k) (α β : P), Commute (xJM k EM j : Module.End k (Tens R P M n)) (diagX k w α β)
def Iteration : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [IsAddTorsionFree V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ) (h : Fin n → R × P) (z : Tens R P S.W n),
    (∀ σ, perm k σ z = z) → S.Ew h (S.mu n z) = n.factorial • ((AA k S.EW n S.w z h : S.W) : V)
def NmSpec : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R] [Fintype P]
    (n : ℕ) (z : Tens R P M n), NmS k (toSym k z) = ∑ σ : Equiv.Perm (Fin n), perm k σ z
def ToSymSurj : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R] [Fintype P]
    (n : ℕ), Function.Surjective (toSym k : Tens R P M n →ₗ[k] (Sym (R × P) n → M))
def ActSpec : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ),
    (∀ (m : Sym (R × P) n) (u : S.W), S.act n (Pi.single m u) = S.Fs m (u : V)) ∧
      ∀ z : Tens R P S.W n, S.act n (toSym k z) = S.mu n z
def NoFactorial : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ),
    ∃ AAS : Module.End k (Sym (R × P) n → S.W),
      (∀ z : Tens R P S.W n, AAS (toSym k z) = toSym k (AA k S.EW n S.w z)) ∧
        (∀ y, NmS k (AAS y) = AA k S.EW n S.w (NmS k y)) ∧
        ∀ y m, S.iota n (S.act n y) m = ((AAS y m : S.W) : V)
def IotaMu : Prop :=
  ∀ (k V P R : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n) (m : Sym (R × P) n),
    S.iota n (S.mu n z) m = ((toSym k (AA k S.EW n S.w z) m : S.W) : V)
def IntegralQuotient : Prop :=
  ∀ (O K M I : Type) [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup M] [Module O M] [Module K M]
    [IsScalarTower O K M] (n : ℕ) (c : Fin n → Module.End O M), (∀ a b, Commute (c a) (c b)) →
    ∀ (Mt : I → Submodule K M) (χ : I → Fin n → K), (∀ τ a, ∀ m ∈ Mt τ, c a m = χ τ a • m) →
    ∀ Dn : O[X], (∀ τ, (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]) ∣ Dn.map (algebraMap O K)) →
    ∀ w : O, ∃ Q ∈ Algebra.adjoin O (Set.range c), ∀ m ∈ ⨆ τ, Mt τ,
      Dn.eval w • m = (w ^ n • (1 : Module.End O M) + ∑ a : Fin n, w ^ a.val • c a) (Q m)
def IntegralLattice : Prop :=
  ∀ (O K M I : Type) [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup M] [Module O M] [Module K M]
    [IsScalarTower O K M] (n : ℕ) (c : Fin n → Module.End O M), (∀ a b, Commute (c a) (c b)) →
    ∀ (Mt : I → Submodule K M) (χ : I → Fin n → K), (∀ τ a, ∀ m ∈ Mt τ, c a m = χ τ a • m) →
    ∀ Dn : O[X], (∀ τ, (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]) ∣ Dn.map (algebraMap O K)) →
    ∀ Lam0 : Submodule O M, (∀ a, ∀ m ∈ Lam0, c a m ∈ Lam0) →
    (∀ a, ∀ m ∈ Lam0, m ∈ ⨆ τ, Mt τ → c a m ∈ Lam0 ∧ c a m ∈ ⨆ τ, Mt τ) ∧
    ∀ w : O, ∀ m ∈ Lam0, m ∈ ⨆ τ, Mt τ → ∃ m' ∈ Lam0, m' ∈ ⨆ τ, Mt τ ∧
      Dn.eval w • m = (w ^ n • (1 : Module.End O M) + ∑ a : Fin n, w ^ a.val • c a) m'
def Conclusion : Prop :=
  ∀ (O V W B X : Type) [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W] [AddCommGroup X]
    (iota : V →ₗ[O] (B → W)) (nab Del : Submodule O V) (nabL DelL : Submodule O W)
    (wtV : X → Submodule O V) (wtW : X → Submodule O W) (bt : B → X) (xi : X →+ ℤ) (lam : X)
    (A Q : Module.End O (B → W)) (D l : O) (e : ℕ) (i' : ℤ),
    Function.Injective iota →
    (∀ v ∈ nab, ∀ α, iota v α ∈ nabL) →
    (∀ ν, ∀ v ∈ wtV ν, ∀ α, iota v α ∈ wtW (ν + bt α)) →
    (∀ α, 0 ≤ xi (bt α)) →
    (∀ v ∈ nab, ∀ α, Q (iota v) α ∈ nabL) →
    (∀ ν z, (∀ α, z α ∈ wtW (ν + bt α)) → ∀ α, Q z α ∈ wtW (ν + bt α)) →
    (∀ v ∈ nab, D • iota v = A (Q (iota v))) →
    (∀ z, (∀ α, z α ∈ DelL) → ∃ v ∈ Del, iota v = A z) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ nabL, u ∈ wtW κ → l ^ e • u ∈ DelL) →
    ∀ ν, xi (lam - ν) ≤ i' → ∀ v ∈ nab, v ∈ wtV ν →
      (l ^ e * D) • v ∈ Del ∧ ∀ (a : ℕ) (η : O), IsUnit η → D = η * l ^ a → l ^ (e + a) • v ∈ Del
def beta {R P : Type*} [DecidableEq R] [DecidableEq P] {n : ℕ} (m : Sym (R × P) n) : P ⊕ R → ℤ :=
  Sum.elim (fun α => (Multiset.countP (fun v : R × P => v.2 = α) m.1 : ℤ))
    (fun b => -(Multiset.countP (fun v : R × P => v.1 = b) m.1 : ℤ))
def HidaSetting.wt {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) (κ : P ⊕ R → ℤ) : Submodule k V :=
  ⨅ a, LinearMap.ker (S.E a a - (κ a : k) • (1 : Module.End k V))
def HidaSetting.DeltaN {O K V P R : Type*} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R) (n : ℕ)
    (DelL : Submodule O S.W) : Submodule O V :=
  Submodule.span O {x | ∃ (m : Sym (R × P) n) (u : S.W), u ∈ DelL ∧ x = ((mfact m : K)⁻¹) • S.Fs m (u : V)}
def CoeffOps : Prop :=
  ∀ (O K R P M : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup M] [Module K M] [Module O M]
    [IsScalarTower O K M] [DecidableEq R] [DecidableEq P] [Fintype R] [Fintype P]
    (EM : R → R → Module.End K M), GlRel EM → ∀ n : ℕ,
    ∃ c : Fin n → Module.End K (Sym (R × P) n → M),
      (∀ (a : Fin n) (z : Tens R P M n), c a (toSym K z) = toSym K ((AApoly K EM n).coeff a.val z)) ∧
      (∀ a b, Commute (c a) (c b)) ∧
      (∀ (t : K) (z : Tens R P M n), toSym K (AA K EM n t z) =
        (t ^ n • (1 : Module.End K (Sym (R × P) n → M)) + ∑ a : Fin n, t ^ a.val • c a) (toSym K z)) ∧
      ∀ L : Sym (R × P) n → Submodule O M,
        (∀ (j : Fin n) (z : Tens R P M n), (∀ g, z g ∈ L (cont g)) → ∀ g, xJM K EM j z g ∈ L (cont g)) →
        ∀ (a : Fin n) (y : Sym (R × P) n → M), (∀ m, y m ∈ L m) → ∀ m, c a y m ∈ L m
def XLattice : Prop :=
  ∀ (O K R P M : Type) [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup M] [Module K M] [Module O M]
    [IsScalarTower O K M] [DecidableEq R] [DecidableEq P] [Fintype R]
    (EM : R → R → Module.End K M) (L : Submodule O M), (∀ b b', ∀ u ∈ L, EM b b' u ∈ L) →
    ∀ (n : ℕ) (j : Fin n) (z : Tens R P M n), (∀ g, z g ∈ L) → ∀ g, xJM K EM j z g ∈ L
def XWeight : Prop :=
  ∀ (k V P R : Type) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (ν : P ⊕ R → ℤ) (j : Fin n) (z : Tens R P S.W n),
    (∀ g, ((z g : S.W) : V) ∈ S.wt (ν + beta (cont g))) →
    ∀ g, ((xJM k S.EW j z g : S.W) : V) ∈ S.wt (ν + beta (cont g))
def IotaWeight : Prop :=
  ∀ (k V P R : Type) [Field k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R]
    (S : HidaSetting k V P R) (n : ℕ) (ν : P ⊕ R → ℤ) (v : V) (m : Sym (R × P) n),
    v ∈ S.wt ν → S.iota n v m ∈ S.wt (ν + beta m)
def BetaDominant : Prop :=
  ∀ (P R : Type) [DecidableEq P] [DecidableEq R] (xi : (P ⊕ R → ℤ) →+ ℤ),
    (∀ (α : P) (b : R), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    ∀ (n : ℕ) (m : Sym (R × P) n), 0 ≤ xi (beta m)
def ActLattice : Prop :=
  ∀ (O K V P R : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R) (n : ℕ)
    (DelL : Submodule O S.W) (y : Sym (R × P) n → S.W), (∀ m, y m ∈ DelL) → S.act n y ∈ S.DeltaN n DelL
def LemmaDSkeleton : Prop :=
  ∀ (O K V P R I : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] [DecidableEq P] [DecidableEq R] [Fintype P] [Fintype R] (S : HidaSetting K V P R) (n : ℕ)
    (wO : O) (nabL DelL : Submodule O S.W) (Mt : I → Submodule K (Sym (R × P) n → S.W)) (χ : I → Fin n → K)
    (Dn : O[X]) (xi : (P ⊕ R → ℤ) →+ ℤ) (lam : P ⊕ R → ℤ) (l : O) (e : ℕ) (i' : ℤ),
    S.w = algebraMap O K wO →
    (∀ b b', ∀ u ∈ nabL, S.EW b b' u ∈ nabL) →
    (∀ z : Tens R P S.W n, (∀ m, S.iota n (S.mu n z) m = 0) → S.mu n z = 0) →
    (∀ (τ : I) (a : Fin n) (z : Tens R P S.W n), toSym K z ∈ Mt τ →
      toSym K ((AApoly K S.EW n).coeff a.val z) = χ τ a • toSym K z) →
    (∀ τ, (X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val : K[X]) ∣ Dn.map (algebraMap O K)) →
    (∀ z : Tens R P S.W n, toSym K (AA K S.EW n S.w z) ∈ ⨆ τ, Mt τ) →
    (∀ (α : P) (b : R), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ nabL, (u : V) ∈ S.wt κ → l ^ e • u ∈ DelL) →
    ∀ ν, xi (lam - ν) ≤ i' → ∀ z : Tens R P S.W n, S.mu n z ∈ S.wt ν →
      (∀ m, ∃ u ∈ nabL, S.iota n (S.mu n z) m = (u : V)) →
      (l ^ e * Dn.eval wO) • S.mu n z ∈ S.DeltaN n DelL
def CasimirStep : Prop :=
  ∀ (A R : Type) [Ring A] [Fintype R] (ε : ℕ → R → R → A),
    (∀ i j, i ≠ j → ∀ a b c d, Commute (ε i a b) (ε j c d)) → ∀ j : ℕ,
    (∑ b, ∑ b', (∑ i ∈ Finset.range (j + 1), ε i b b') * (∑ i ∈ Finset.range (j + 1), ε i b' b)) -
        (∑ b, ∑ b', (∑ i ∈ Finset.range j, ε i b b') * (∑ i ∈ Finset.range j, ε i b' b)) =
      2 • (∑ a ∈ Finset.range j, ∑ b, ∑ b', ε a b b' * ε j b' b) + ∑ b, ∑ b', ε j b b' * ε j b' b
def CasimirY : Prop :=
  ∀ (k R P M : Type) [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R] (n : ℕ)
    (j : Fin n), ∑ b, ∑ b', unitY k j b b' * unitY k j b' b = Fintype.card R • (1 : Module.End k (Tens R P M n))
def CasimirValue : Prop :=
  ∀ (k M : Type) [CommRing k] [AddCommGroup M] [Module k M] (r : ℕ) (T : Fin r → Fin r → Module.End k M), GlRel T →
    ∀ (v : M) (κ : Fin r → k), (∀ b b', b < b' → T b b' v = 0) → (∀ b, T b b v = κ b • v) →
    (∑ b, ∑ b', T b b' * T b' b) v = (∑ b : Fin r, κ b * (κ b + (r : k) - 1 - 2 * (b.val : k))) • v
def CasimirContent : Prop :=
  ∀ (r : ℕ) (κ : Fin r → ℤ) (ρ : Fin r),
    (∑ b : Fin r, (κ b + if b = ρ then 1 else 0) * ((κ b + if b = ρ then 1 else 0) + (r : ℤ) - 1 - 2 * (b.val : ℤ))) -
        (∑ b : Fin r, κ b * (κ b + (r : ℤ) - 1 - 2 * (b.val : ℤ))) - (r : ℤ) = 2 * (κ ρ - (ρ.val : ℤ))
noncomputable def DnPoly (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range (q + w + i), (X - C ((k : ℤ) - (q : ℤ))) ^ LD.mu p w i lam2 ((k : ℤ) - (q : ℤ))
noncomputable def shapePoly {q : ℕ} (lam2 tau : Fin q → ℕ) : ℤ[X] :=
  ∏ a : Fin q, ∏ j ∈ Finset.Ico (lam2 a) (tau a), (X - C ((j : ℤ) - (a.val : ℤ)))
def DnPolyEval : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), (DnPoly p w i lam2).eval (w : ℤ) = LD.Dn p w i lam2
def ShapeDvd : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), (∀ b, lam2 b ≤ w) → ∀ tau ∈ LD.shapes p w i lam2,
    (shapePoly lam2 tau).Monic ∧ (shapePoly lam2 tau).natDegree = i ∧ shapePoly lam2 tau ∣ DnPoly p w i lam2
end Formalism.CohomologicalDescent.Symmetrization


