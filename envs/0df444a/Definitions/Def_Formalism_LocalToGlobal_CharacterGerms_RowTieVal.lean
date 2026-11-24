-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieVal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:08.285206+00:00
-- url     : https://prove2.me/theorems/cdd045d3-43ab-48f1-b684-d6aec74cc46f
-- title:
--   Row Tie Val
-- statement:
--   Definitions and structural lemmas for Row Tie Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieVal.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
structure LetSys (C : Type) [Field C] (dd : ℕ) where
  ι : ℕ → Type
  fin : ∀ N, Fintype (ι N)
  cp : ∀ N, ι N → Fin N
  uv : ∀ N, ι N → Fin dd → C
  FF : ∀ N, Set (MvPolynomial (ι N) C)
attribute [instance] LetSys.fin
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def FBChart.nab (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (f : PS C n dd) (P : MvPolynomial (Ls.ι n) C) : C :=
  nabValN Y.B C Y.h Y.w0 Y.k f (Ls.cp n) (Ls.uv n) P
def FBChart.valSet (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : Set (WithTop ℝ) :=
  {x | ∃ P ∈ Ls.FF n, ∃ f : PS C n dd, IntS V f ∧ x = V.v (Y.nab Ls n f P)}
def FBChart.nuPl (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : WithTop ℝ := sInf (Y.valSet Ls n)
def FBChart.nuPlE (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : EReal :=
  ⨅ x ∈ Y.valSet Ls n, (WithBot.some x : WithBot (WithTop ℝ))
variable {d : ℕ} [NeZero d]
section One
variable {I : Fin 2 → Type} [∀ g, Fintype (I g)]
def IsImg (X : RawChart C d I (Fin dd)) {N : ℕ} {ι : Type} (cp : ι → Fin N) (uv : ι → Fin dd → C)
    (P : MvPolynomial ι C) (Q : MvPolynomial (Fin N × WV I) C) : Prop :=
  ∃ co : ι → WV I → C, (∀ ℓ ∈ P.vars, uv ℓ = ∑ w : WV I, co ℓ w • X.u w.1 w.2) ∧
    Q = MvPolynomial.aeval
      (fun ℓ => ∑ w : WV I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) P
variable (Y : FBChart C V O dd) (p : PairData Y d I) (H : (Y.raw p).Hyps V) (Ls : LetSys C dd) (n : ℕ)
def ValEqSt : Prop :=
  ∀ P ∈ Ls.FF n, ∀ Q, IsImg (Y.raw p) (Ls.cp n) (Ls.uv n) P Q →
    ∀ kind : Fin n → Option (Fin 2 × ZMod d × ZMod d),
    RowsOK ((Y.raw p).rowData H).G ((Y.raw p).rowData H).Alt Q kind →
    ∀ (S : ∀ g, Sys (((Y.raw p).rowData H).G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ gr : Fin n → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) →
      ∃ f : PS C n dd, IntS V f ∧ Y.nab Ls n f P = ValOf ((Y.raw p).rowData H).hL Q kind gr
def rowValue (hb : BddBelow (Y.valSet Ls n)) (hv : ValEqSt Y p H Ls n) : RowValue ((Y.raw p).rowData H) where
  nu := Y.nuPl Ls n
  FF := fun N => {Q | ∃ e : N = n, ∃ P ∈ Ls.FF n, IsImg (Y.raw p) (Ls.cp n) (Ls.uv n) P (e ▸ Q)}
  VAL := by
    rintro N Q ⟨rfl, P, hP, hQ⟩ kind hk S t ht gr hg
    obtain ⟨f, hf, e⟩ := hv P hP Q hQ kind hk S t ht gr hg
    rw [← e]
    exact csInf_le hb ⟨P, hP, f, hf, rfl⟩
end One
section Orb
variable {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
abbrev WVO (I : Orb → Fin 2 → Type) := Σ o : Orb, WV (I o)
def IsImgO (X : ∀ o, RawChart C d (I o) (Fin dd)) {N : ℕ} {ι : Type} (cp : ι → Fin N) (uv : ι → Fin dd → C)
    (P : MvPolynomial ι C) (Q : MvPolynomial (Fin N × WVO I) C) : Prop :=
  ∃ co : ι → WVO I → C, (∀ ℓ ∈ P.vars, uv ℓ = ∑ w : WVO I, co ℓ w • (X w.1).u w.2.1 w.2.2) ∧
    Q = MvPolynomial.aeval
      (fun ℓ => ∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) P
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
def PairsSep : Prop :=
  ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0
def toAll {N : ℕ} (o : Orb) (Q : MvPolynomial (Fin N × WV (I o)) C) : MvPolynomial (Fin N × WVO I) C :=
  MvPolynomial.rename (fun x : Fin N × WV (I o) => (x.1, (⟨o, x.2⟩ : WVO I))) Q
def ValEqPSt : Prop :=
  PairsSep Y p → ∀ P ∈ Ls.FF n, ∀ Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C,
    IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)) →
    ∀ kind : Orb → Fin n → Option (Fin 2 × ZMod d × ZMod d),
    (∀ o, RowsOK ((Y.raw (p o)).rowData (H o)).G ((Y.raw (p o)).rowData (H o)).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys (((Y.raw (p o)).rowData (H o)).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C),
    (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      ∃ f : PS C n dd, IntS V f ∧
        Y.nab Ls n f P = ∏ o, ValOf ((Y.raw (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)
end Orb
end Formalism.L2.FormalSeriesBounds


