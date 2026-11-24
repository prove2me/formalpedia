-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
-- name    : Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:35.736544+00:00
-- url     : https://prove2.me/theorems/d473b073-3171-4eea-bcc8-f2bc9f344ace
-- title:
--   Host Trace Identity
-- statement:
--   Definitions and structural lemmas for Host Trace Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/HostTraceIdentity.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
def VF.RR {C : Type} [Field C] (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
section Chart
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
def a3B (C3 : IntChart T io y) : FB T.Fr (chD C3.ch) (𝓞 E) := letI := io.toAlgebra; C3.ch.B
def a3h (C3 : IntChart T io y) : PS T.Fr 2 (chD C3.ch) := letI := io.toAlgebra; C3.ch.h
def chartUnitVectors (C3 : IntChart T io y) : Lt1 Dw → Fin (chD C3.ch) → T.Fr := letI := io.toAlgebra; C3.ch.uvec
def EmbOK (T : CDVR) (V : VF C) (ι : T.Fr →+* C) : Prop :=
  ∀ x : T.Fr, x ≠ 0 → V.v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)
def eOf (T : CDVR) (V : VF C) : ℕ := (vV T.V ((V.l : ℕ) : T.Fr)).toNat
structure IsBC (C3 : IntChart T io y) (ι : T.Fr →+* C) (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)) : Prop where
  F : ∀ j, Y.B.G.F j = MvPowerSeries.map ι ((a3B C3).G.F j)
  act : ∀ a j, Y.B.A.act a j = MvPowerSeries.map ι ((a3B C3).A.act a j)
  ph1 : Y.B.ph1 = MvPowerSeries.map ι (a3B C3).ph1
  ph2 : Y.B.ph2 = MvPowerSeries.map ι (a3B C3).ph2
  sy : Y.B.sy = MvPowerSeries.map ι (a3B C3).sy
  ad : ∀ a, Y.B.ad a = MvPowerSeries.map ι ((a3B C3).ad a)
  h : Y.h = MvPowerSeries.map ι (a3h C3)
  w0 : Y.w0 = H.w0
  k : Y.k = k
def chartLetterSystem (C3 : IntChart T io y) (V : VF C) (ι : T.Fr →+* C) (a : (E →+* ℂ) × ℕ → ℕ) : LetSys C (chD C3.ch) where
  ι := fun N => LtN Dw N
  fin := fun _ => inferInstance
  cp := fun _ ℓ => ℓ.2.2
  uv := fun _ ℓ i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)
  FF := fun N => HaO Dw.mult N C V.RR ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)
end Chart
structure Lab (E : Type) [Field E] (Orb : Type) (d : ℕ) where
  tau : Orb → Fin 2 → ZMod d → (E →+* ℂ)
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop
abbrev Lab.II {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) (o : Orb) (g : Fin 2) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o g a))
section Pairs
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]
def emA3 (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (τ : E →+* ℂ) : 𝓞 E →+* C := (ι.comp io).comp (embK c τ)
def lieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : Lab E Orb d) (o : Orb) (g : Fin 2) (x : lab.II Dw o g) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o g x.1, x.2⟩ i)
structure LabArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : Lab E Orb d) : Prop where
  inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2
  conj : ∀ o a, lab.tau o 1 a = ComplexEmbedding.conjugate (lab.tau o 0 a)
  frob : ∀ o g a x, V.MM (emA3 io ι (lab.tau o g (a + 1)) x - emA3 io ι (lab.tau o g a) x ^ V.l)
  sep : ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2.1 x.2.2) a - emA3 io ι (lab.tau x'.1 x'.2.1 x'.2.2) a) = 0
  unr : ∀ o g, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o g a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o g a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y
structure LabGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : Lab E Orb d) :
    Prop where
  em_int : ∀ o g a x, V.Ge 0 (emA3 io ι (lab.tau o g a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o 1 a) x = emA3 io ι (lab.tau o 0 a) (star x)
  u_int : ∀ o g x i, V.Ge 0 (lieBasisVector C3 ι lab o g x i)
  u_eig : ∀ o g (x : lab.II Dw o g) a, linAct (Y.B.A.act a) (lieBasisVector C3 ι lab o g x) =
    emA3 io ι (lab.tau o g x.1) a • lieBasisVector C3 ι lab o g x
  u_sat : ∀ o g, ∃ w : Fin (chD C3.ch) → lab.II Dw o g → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o g, ∑ x, lieBasisVector C3 ι lab o g q x * w x q' = if q = q' then 1 else 0
  u_full : ∀ o g a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o g a) x • v) →
    ∃ b : lab.II Dw o g → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • lieBasisVector C3 ι lab o g q
def pairOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (o : Orb) : PairData Y d (lab.II Dw o) where
  em := fun g a => emA3 io ι (lab.tau o g a)
  em_int := hg.em_int o
  em_conj := hg.em_conj o
  em_frob := ha.frob o
  em_sep := fun p p' hp => ha.sep (o, p) (o, p') (fun h => hp (Prod.mk.inj h).2)
  em_unr := ha.unr o
  u := lieBasisVector C3 ι lab o
  ty := fun _ x => x.1
  u_int := hg.u_int o
  u_eig := hg.u_eig o
  u_sat := fun g => by
    obtain ⟨w, h1, h2⟩ := hg.u_sat o g
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  u_full := hg.u_full o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o
end Pairs
section Named
variable (Xo c)
def BCExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    H.w0 + star H.w0 = 1 → ∀ k : ℕ, V.v (k : C) = 0 → ∃ Y : FBChart C V (𝓞 E) (chD C3.ch), IsBC C3 ι k Y
def HostTraceIdentity (H : Host E) : Prop := (∀ a : 𝓞 E, star a = H.bar a) → H.w0 + star H.w0 = 1
def DescentSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C3 (eOf T V) k a n ≤ Y.nuPlE (chartLetterSystem C3 V ι a) n
def LabGeoSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → LabGeo C3 ι Y lab
end Named
def Lab.RankOK {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ g a, lab.big o g a → Dw.mult (lab.tau o g a) = lab.n + lab.j) ∧
    (∀ g a, ¬ lab.big o g a → Dw.mult (lab.tau o g a) = lab.j')
section Top
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]
end Top
end Formalism.L2.FormalSeriesBounds


