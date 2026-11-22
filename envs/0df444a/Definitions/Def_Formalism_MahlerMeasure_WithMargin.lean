-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_WithMargin
-- name    : Formalism_MahlerMeasure_WithMargin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:37.764972+00:00
-- url     : https://prove2.me/theorems/44ff135b-80cb-4584-98ad-3c6c745eeaf6
-- title:
--   With Margin
-- statement:
--   Definitions and structural lemmas for With Margin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/WithMargin.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_TieVars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
abbrev BVar (N r t : ℕ) := (Fin (N + 1) × Fin r) ⊕ (Fin (t + 1) × Bool)
structure BlockData (N : ℕ) where
  LL : Letters N
  T : TieData
  uPos : Fin N
  B : ℕ
  zPlus : ℕ
variable {N r : ℕ}
def finPos (N : ℕ) (k : ℕ) : Fin (N + 1) := ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩
def BlockData.lettersAt (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : Letters N where
  vec := D.LL.vec
  deg := fun a => D.LL.deg a - (∑ i, if (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1 then j i else 0) -
    (if a = D.uPos then jp else 0)
def BlockData.withMargin (D : BlockData N) (cap : Fin D.T.q → WithTop ℤ) (m : ℕ) : BlockData N :=
  { D with T := { D.T with thr := fun k => (cap k).map (fun x => x - (m : ℤ)) } }
def chainEmb (N r t : ℕ) : Fin N × Fin r → BVar N r t := fun x => Sum.inl (Fin.castSucc x.1, x.2)
def xiVar (N r t : ℕ) (c : Fin r) : BVar N r t := Sum.inl (Fin.last N, c)
def scalZ (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, false)
def scalS (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, true)
noncomputable def BlockData.Ehat (p : ℕ) [Fact p.Prime] (D : BlockData N) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
    ∑ c, X (Sum.inl (finPos N (D.T.pos i), c)) * X (Sum.inl (finPos N (D.T.pos i + 1), c))
noncomputable def BlockData.Eplus (p : ℕ) [Fact p.Prime] (D : BlockData N) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  X (scalZ N r D.T.t (Fin.last D.T.t)) * X (scalS N r D.T.t (Fin.last D.T.t)) +
    ∑ c, X (Sum.inl (Fin.castSucc D.uPos, c)) * X (xiVar N r D.T.t c)
noncomputable def XiPolZ (p : ℕ) [Fact p.Prime] (N r t b : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r t) ℚ_[p]) :=
  (MvPolynomial.restrictSupport ℚ_[p]
      {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}).restrictScalars ℤ_[p] ⊓
    IntPol p (BVar N r t)
def BlockData.LevelOK (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : Prop :=
  (∀ i, j i ≤ D.LL.deg (⟨min (D.T.pos i) (N - 1), by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd D.uPos.2 (by omega)
      · omega⟩) ∧ j i ≤ D.LL.deg (⟨min (D.T.pos i + 1) (N - 1), by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd D.uPos.2 (by omega)
      · omega⟩)) ∧ jp ≤ min (D.LL.deg D.uPos) D.B
def BlockData.gens (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Set (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
    x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      rename (chainEmb N r D.T.t) y * g}
noncomputable def BlockData.SSZ (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) :
    Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens p (r := r) j jp)
noncomputable def BlockData.Pall (p : ℕ) [Fact p.Prime] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus
    ((List.finRange D.T.t).foldr (fun i acc =>
      tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
        (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
        ((D.lettersAt j jp).deg (⟨min (D.T.pos i) (N - 1), by
            rcases Nat.eq_zero_or_pos N with h | h
            · exact absurd D.uPos.2 (by omega)
            · omega⟩))
        ((D.lettersAt j jp).deg (⟨min (D.T.pos i + 1) (N - 1), by
            rcases Nat.eq_zero_or_pos N with h | h
            · exact absurd D.uPos.2 (by omega)
            · omega⟩))
        (D.T.z i) acc) y)
noncomputable def BlockData.PSZ (p : ℕ) [Fact p.Prime] [NeZero r] (D : BlockData N) :
    Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp),
    {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
      x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g)})
end Formalism.GM.M


