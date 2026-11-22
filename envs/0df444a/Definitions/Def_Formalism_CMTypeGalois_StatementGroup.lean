-- Prove2me | Definitions.Def_Formalism_CMTypeGalois_StatementGroup
-- name    : Formalism_CMTypeGalois_StatementGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:41.690856+00:00
-- url     : https://prove2.me/theorems/d9f80cf5-959a-4534-9fbf-bff6e1170e21
-- title:
--   Statement Group
-- statement:
--   Definitions and structural lemmas for Statement Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/StatementGroup.lean

import Mathlib
import Definitions.Def_Formalism_StatementCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.Q3
def IsCMTypeG {G : Type*} [Mul G] (c : G) (Φ : Finset G) : Prop := ∀ g : G, g ∈ Φ ↔ c * g ∉ Φ
instance {G : Type*} [Mul G] [Fintype G] [DecidableEq G] (c : G) : DecidablePred (IsCMTypeG c) :=
  fun _ => Fintype.decidableForallFintype
def dualTypeG {G : Type*} [Monoid G] [DecidableEq G] (c : G) (Φ : Finset G) : Finset G :=
  insert 1 ((Φ.erase 1).image (fun g => c * g))
def countsG {G : Type*} (c : G) (Φ : Finset G) (σ : G) : Prop := σ ∉ Φ ∧ σ ≠ c
def stabG {G : Type*} [Mul G] [Fintype G] [DecidableEq G] (Φ : Finset G) : Finset G :=
  univ.filter (fun h => ∀ g ∈ Φ, h * g ∈ Φ)
def CMTypeCount : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 →
    (univ.filter (fun Φ : Finset G => IsCMTypeG c Φ)).card = 2 ^ (Fintype.card G / 2) ∧
    (univ.filter (fun Φ : Finset G => IsCMTypeG c Φ ∧ 1 ∈ Φ)).card = 2 ^ (Fintype.card G / 2 - 1)
def TwoTypesG : Prop :=
  ∀ (G : Type) [CommGroup G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 →
  ∀ Φ : Finset G, IsCMTypeG c Φ → 1 ∈ Φ →
    IsCMTypeG c (dualTypeG c Φ) ∧ 1 ∈ dualTypeG c Φ ∧
    (∀ σ : G, σ ≠ 1 → σ ≠ c → (countsG c Φ σ ↔ ¬ countsG c (dualTypeG c Φ) σ)) ∧
    (∀ s : G, ((if s ∉ Φ then 1 else 0) + (if s ∉ dualTypeG c Φ then 1 else 0) : ℤ)
        = 1 - (if s = 1 then 1 else 0) + (if s = c then 1 else 0))
def HalfTypesG : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 →
  ∀ σ : G, σ ≠ 1 → σ ≠ c →
    2 * (univ.filter (fun Φ : Finset G => IsCMTypeG c Φ ∧ 1 ∈ Φ ∧ σ ∉ Φ ∧ σ ≠ c)).card
      = (univ.filter (fun Φ : Finset G => IsCMTypeG c Φ ∧ 1 ∈ Φ)).card
def FlipParity : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 →
  (∀ Φ : Finset G, IsCMTypeG c Φ → 1 ∈ Φ →
      Φ \ dualTypeG c Φ = Φ.erase 1 ∧ (Φ \ dualTypeG c Φ).card = Fintype.card G / 2 - 1) ∧
  ∀ ε : Finset G → ℤˣ,
    (∀ Φ Ψ : Finset G, IsCMTypeG c Φ → IsCMTypeG c Ψ → (Φ \ Ψ).card = 1 → ε Ψ = -ε Φ) →
    ∀ Φ : Finset G, IsCMTypeG c Φ → 1 ∈ Φ →
      ε (dualTypeG c Φ) = (-1) ^ (Fintype.card G / 2 - 1) * ε Φ
open Classical in

def OddCharSum : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G] (c : G), c ≠ 1 → c * c = 1 → ∀ s : G,
    ∑ ψ ∈ univ.filter (fun ψ : AddChar (Additive G) ℂ => ψ (Additive.ofMul c) = -1),
        ψ (Additive.ofMul s)
      = ((Fintype.card G : ℂ) / 2) * ((if s = 1 then 1 else 0) - (if s = c then 1 else 0))
def LinkCM : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], ∀ Φ : Finset (ZMod l)ˣ,
    (IsCMTypeG (-1) Φ ↔ Formalism.IsCMType Φ) ∧ dualTypeG (-1) Φ = Formalism.dualType Φ ∧
    ∀ σ : (ZMod l)ˣ, (countsG (-1) Φ σ ↔ Formalism.counts Φ σ)
def GeneralImpliesCM : Prop := (TwoTypesG → Formalism.TwoTypes) ∧ (HalfTypesG → Formalism.HalfTypes)
abbrev Gal3 := Fin 3 → ℤˣ
def cc : Gal3 := fun _ => -1
def chiS (S : Finset (Fin 3)) (g : Gal3) : ℤˣ := ∏ i ∈ S, g i
def kerChi (S : Finset (Fin 3)) : Finset Gal3 := univ.filter (fun g => chiS S g = 1)
def TriEnumeration : Prop :=
  (∀ S : Finset (Fin 3), chiS S cc = (-1) ^ S.card) ∧
  (univ.filter (fun S : Finset (Fin 3) => Odd S.card)).card = 4 ∧
  (univ.filter (fun S : Finset (Fin 3) => S.Nonempty ∧ Even S.card)).card = 3 ∧
  (∀ g : Gal3, ∀ D : ℕ, g ^ D = cc ↔ g = cc ∧ Odd D) ∧
  (∀ g : Gal3, g ≠ 1 → orderOf g = 2) ∧
  (univ.filter (fun Φ : Finset Gal3 => IsCMTypeG cc Φ)).card = 16 ∧
  (∀ Φ : Finset Gal3, IsCMTypeG cc Φ → (stabG Φ).card = 1 ∨ (stabG Φ).card = 4) ∧
  (univ.filter (fun Φ : Finset Gal3 => IsCMTypeG cc Φ ∧ (stabG Φ).card = 4)).card = 8 ∧
  (univ.filter (fun Φ : Finset Gal3 => IsCMTypeG cc Φ ∧ (stabG Φ).card = 1)).card = 8 ∧
  (∀ S : Finset (Fin 3), Odd S.card →
      (univ.filter (fun Φ : Finset Gal3 => IsCMTypeG cc Φ ∧ stabG Φ = kerChi S)).card = 2) ∧
  (∀ Φ : Finset Gal3, IsCMTypeG cc Φ → (stabG Φ).card = 4 →
      ∃ S : Finset (Fin 3), Odd S.card ∧ stabG Φ = kerChi S ∧
        (Φ = kerChi S ∨ Φ = (kerChi S).image (fun g => cc * g))) ∧
  (∀ Φ : Finset Gal3, IsCMTypeG cc Φ → 1 ∈ Φ → ∀ s : Gal3,
      ((if s ∉ Φ then 1 else 0) + (if s ∉ dualTypeG cc Φ then 1 else 0) : ℚ)
        = 1 - (1 / 4) * ∑ S ∈ univ.filter (fun S : Finset (Fin 3) => Odd S.card),
            (((chiS S s : ℤˣ) : ℤ) : ℚ))
def chiQ (q : ℕ) (n : ℤ) : ℤ := jacobiSym n q
def Hyp3 (q : Fin 3 → ℕ) : Prop := (∀ i, (q i).Prime ∧ q i % 4 = 3) ∧ Function.Injective q
def HostPrimes (q : Fin 3 → ℕ) : Prop :=
  Hyp3 q ∧ jacobiSym (q 0) (q 1) = 1 ∧ jacobiSym (q 1) (q 2) = 1 ∧ jacobiSym (q 2) (q 0) = 1
def KroneckerMeaning : Prop :=
  ∀ q : ℕ, q.Prime → q % 4 = 3 →
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ q → chiQ q p = jacobiSym (-(q : ℤ)) p) ∧
    (chiQ q 2 = 1 ↔ q % 8 = 7) ∧ chiQ q (-1) = -1
def e3 (i : Fin 3) : Gal3 := Pi.mulSingle i (-1)
def sgn (z : ℤ) : ℤˣ := if z = 1 then 1 else -1
def frobVec (q : Fin 3 → ℕ) (i : Fin 3) : Gal3 :=
  fun j => if j = i then 1 else sgn (chiQ (q j) (q i))
def modelDecomp (q : Fin 3 → ℕ) (i : Fin 3) : Subgroup Gal3 :=
  Subgroup.closure {e3 i, frobVec q i}
def HostTable : Prop :=
  ∀ q : Fin 3 → ℕ, HostPrimes q →
    (∀ i j : Fin 3, i ≠ j → jacobiSym (-(q j : ℤ)) (q i) = chiQ (q j) (q i)) ∧
    (chiQ (q 1) (q 0) = 1 ∧ chiQ (q 2) (q 0) = -1) ∧
    (chiQ (q 0) (q 1) = -1 ∧ chiQ (q 2) (q 1) = 1) ∧
    (chiQ (q 0) (q 2) = 1 ∧ chiQ (q 1) (q 2) = -1) ∧
    modelDecomp q 0 = Subgroup.closure {(![-1, 1, 1] : Gal3), ![1, 1, -1]} ∧
    modelDecomp q 1 = Subgroup.closure {(![1, -1, 1] : Gal3), ![-1, 1, 1]} ∧
    modelDecomp q 2 = Subgroup.closure {(![1, 1, -1] : Gal3), ![1, -1, 1]} ∧
    (∀ i : Fin 3, cc ∉ modelDecomp q i) ∧
    (q 0 % 8 = 7 → chiQ (q 0) 2 = 1 ∧ (fun j => sgn (chiQ (q j) 2)) ≠ cc)
def BiquadFails : Prop :=
  ∀ q q' : ℕ, q.Prime → q'.Prime → q % 4 = 3 → q' % 4 = 3 → q ≠ q' →
    ((fun _ => -1 : Fin 2 → ℤˣ) ∈
        Subgroup.closure {(Pi.mulSingle 0 (-1) : Fin 2 → ℤˣ), ![1, sgn (chiQ q' q)]}) ∨
    ((fun _ => -1 : Fin 2 → ℤˣ) ∈
        Subgroup.closure {(Pi.mulSingle 1 (-1) : Fin 2 → ℤˣ), ![sgn (chiQ q q'), 1]})
def CondChar : Prop :=
  ∀ q : Fin 3 → ℕ, Hyp3 q →
    (∀ S : Finset (Fin 3), ∃ χ : DirichletCharacter ℂ (∏ i ∈ S, q i),
      (∀ n : ℤ, χ n = ∏ i ∈ S, (chiQ (q i) n : ℂ)) ∧ χ.IsPrimitive ∧ χ (-1) = (-1) ^ S.card) ∧
    ∏ S : Finset (Fin 3), ∏ i ∈ S, q i = (q 0 * q 1 * q 2) ^ 4
def NonVac : Prop :=
  HostPrimes ![7, 31, 11] ∧ (![7, 31, 11] : Fin 3 → ℕ) 0 % 8 = 7 ∧ ∀ i, 3 < (![7, 31, 11] : Fin 3 → ℕ) i
end Formalism.Q3


