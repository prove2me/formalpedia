-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
-- name    : Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:40.914645+00:00
-- url     : https://prove2.me/theorems/74bda433-3f7a-4f36-8362-70503e9c8539
-- title:
--   Mem Real Cyclotomic Subgroup
-- statement:
--   Definitions and structural lemmas for Mem Real Cyclotomic Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/QuadraticCharacters/MemRealCyclotomicSubgroup.lean

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_ExceptionalCharacterCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace HostParam
namespace AbField
variable (E : AbField)
instance : NeZero E.N := ⟨E.N_pos.ne'⟩
instance : Finite E.Gal := inferInstance
noncomputable instance : Fintype E.Gal := Fintype.ofFinite _
noncomputable def degree : ℕ := Nat.card E.Gal
def frobUnits (p i : ℕ) : Set (ZMod E.N)ˣ :=
  {u | ((ZMod.unitsMap (Nat.ordCompl_dvd E.N p) u : (ZMod (ordCompl[p] E.N))ˣ) :
    ZMod (ordCompl[p] E.N)) = (p : ZMod (ordCompl[p] E.N)) ^ i}
def frobCoset (p i : ℕ) : Set E.Gal := E.res '' E.frobUnits p i
def decomp (p : ℕ) : Subgroup E.Gal := E.inertia p ⊔ Subgroup.closure (E.frobCoset p 1)
def primChars : Set PrimChar := prim '' E.chars
def Sub (E E' : AbField) : Prop := E.primChars ⊆ E'.primChars
def fixedBy (U : Subgroup E.Gal) : AbField := ⟨E.N, E.N_pos, U.comap E.res⟩
def lift (M : ℕ) (hM : 0 < M) (h : E.N ∣ M) : AbField := ⟨M, hM, E.H.comap (ZMod.unitsMap h)⟩
def rat : AbField := ⟨1, one_pos, ⊤⟩
def cyc (N : ℕ) (hN : 0 < N) : AbField := ⟨N, hN, ⊥⟩
def cycReal (N : ℕ) (hN : 0 < N) : AbField := ⟨N, hN, Subgroup.zpowers (-1)⟩
noncomputable def ofChar {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) : AbField :=
  ⟨N, hN, χ.toUnitHom.ker⟩
def HasRoots (m : ℕ) : Prop := ∀ χ : DirichletCharacter ℂ m, prim χ ∈ E.primChars
noncomputable def numRoots : ℕ := sSup {m : ℕ | 0 < m ∧ E.HasRoots m}
end AbField
structure Core where
  e : ℕ
  two_le_e : 2 ≤ e
  E : AbField
  not_real : ¬ E.IsReal
  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_dvd : d ∣ E.N
  K_le : E.chOf d d_dvd ∈ E.chars
  card_inertia_d : Nat.card (E.inertia d) = 2
  ps : DirichletCharacter ℂ E.N
  ps_mem : ps ∈ E.chars
  ps_ne_one : ps ≠ 1
  ps_sq : ps ^ 2 = 1
  ps_odd : ps.Odd
  ps_inertia : ∀ u ∈ E.inertiaUnits d, ps (u : ZMod E.N) = 1
  four_n_dvd : 4 * 2 ^ e ∣ E.N
  attached_subfield_le_adjoin_simple : ∀ u ∈ E.H, ZMod.unitsMap four_n_dvd u = 1 ∨ ZMod.unitsMap four_n_dvd u = -1
  A0 : Subgroup E.Gal
  base_exponent_le_a : A0 ≤ (E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓ (E.toGalChar ps ps_mem).ker
  A0_inf_stabilizer_trivial : ∀ u : (ZMod E.N)ˣ, E.res u ∈ A0 →
    (QuotientGroup.mk (ZMod.unitsMap four_n_dvd u) : GalRealCyclotomic (2 ^ e)) = 1 → E.res u = 1
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → SplitsIn d l
namespace Core
variable (C : Core)
def n : ℕ := 2 ^ C.e
noncomputable def ch : DirichletCharacter ℂ C.E.N := C.E.chOf C.d C.d_dvd
noncomputable def chG : C.E.Gal →* ℂˣ := C.E.toGalChar (C.E.chOf C.d C.d_dvd) C.K_le
noncomputable def psG : C.E.Gal →* ℂˣ := C.E.toGalChar C.ps C.ps_mem
noncomputable def Phi : Subgroup C.E.Gal := C.chG.ker
noncomputable def A : Subgroup C.E.Gal := C.chG.ker ⊓ C.psG.ker
def hG : C.E.Gal →* GalRealCyclotomic (2 ^ C.e) :=
  QuotientGroup.lift C.E.H
    ((QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (4 * 2 ^ C.e))ˣ))).comp
      (ZMod.unitsMap C.four_n_dvd)) (fun u hu => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rcases C.attached_subfield_le_adjoin_simple u hu with h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.mem_zpowers _)
noncomputable def kerh : Subgroup C.E.Gal := C.A ⊓ C.hG.ker
open Classical in

noncomputable def iota : C.E.Gal :=
  if h : ∃ g ∈ C.E.inertia C.d, g ≠ 1 then h.choose else 1
noncomputable def sg : C.E.Gal := C.E.conj * C.iota
noncomputable def G0 : Subgroup C.E.Gal := Subgroup.closure {C.E.conj, C.iota}
open Classical in

noncomputable def comp0 (g : C.E.Gal) : C.E.Gal :=
  if C.chG g = 1 then (if C.psG g = 1 then 1 else C.sg)
  else (if C.psG g = 1 then C.iota else C.E.conj)
noncomputable def compA (g : C.E.Gal) : C.E.Gal := g * (C.comp0 g)⁻¹
def E1 : AbField := C.E.fixedBy (C.E.inertia C.d)
noncomputable def R : AbField := C.E.fixedBy C.G0
noncomputable def f : ℕ := C.E.degree / 2
noncomputable def o : ℕ := (C.A0.subgroupOf C.A).index
noncomputable def oh : ℕ := Nat.card C.kerh
noncomputable def o' : ℕ := (C.A0.map C.hG).index
noncomputable def n0 : ℕ := Nat.card C.A0
def Chat : Set (C.E.Gal →* ℂˣ) := {ξ | (∀ g ∈ C.A0, ξ g = 1) ∧ ∀ g ∈ C.G0, ξ g = 1}
def XplusG : Set (C.E.Gal →* ℂˣ) := {χ | ∃ ξ ∈ C.Chat, χ = ξ ∨ χ = ξ * C.psG}
def XminusG : Set (C.E.Gal →* ℂˣ) := {χ | ∃ ξ ∈ C.XplusG, χ = C.chG * ξ}
def Xplus : Set (DirichletCharacter ℂ C.E.N) :=
  {χ | ∃ hχ : χ ∈ C.E.chars, (∀ g ∈ C.A0, C.E.toGalChar χ hχ g = 1) ∧
    ∀ u ∈ C.E.inertiaUnits C.d, χ (u : ZMod C.E.N) = 1}
end Core
end HostParam


