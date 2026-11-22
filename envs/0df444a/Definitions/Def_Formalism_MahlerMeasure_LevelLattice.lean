-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_LevelLattice
-- name    : Formalism_MahlerMeasure_LevelLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:10.392007+00:00
-- url     : https://prove2.me/theorems/a0027746-1ddb-4652-971b-47462898e5fc
-- title:
--   Level Lattice
-- statement:
--   Definitions and structural lemmas for Level Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/LevelLattice.lean

import Definitions.Def_Formalism_MahlerMeasure_WithMargin
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
variable {N r : ℕ}
def BlockData.BlockOK (D : BlockData N) : Prop :=
  D.T.Admissible D.LL ∧ (∀ i, D.T.pos i + 1 < (D.uPos : ℕ)) ∧ D.LL.vec D.uPos = true ∧ (D.uPos : ℕ) + 1 = N
def BlockData.letterAt (D : BlockData N) (k : ℕ) : Fin N :=
  ⟨min k (N - 1), by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd D.uPos.2 (by omega)
    · omega⟩
noncomputable def BlockData.phiAll (p : ℕ) [Fact p.Prime] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  Formalism.GM.tiePhi (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
            (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus ∘ₗ
    (List.finRange D.T.t).foldr (fun i acc =>
      Formalism.GM.tiePhi (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
        ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
        (D.T.z i) ∘ₗ acc) LinearMap.id
def SSDirect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → 1 ≤ r →
    iSupIndep (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) ∧
    ∀ x, x ∈ Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) →
      x ∈ IntPol p (BVar N r D.T.t) → x ∈ D.SSZ p (r := r)
def LevelLattice : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a : ℕ), D.BlockOK → 1 ≤ r → 1 ≤ a →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → (∀ i, D.T.z i ≤ 2 * a) → D.zPlus ≤ 2 * a →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
        Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr) →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr) →
    Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) =
        Submodule.span ℚ_[p] (D.PSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) ∧
      (∀ x ∈ D.SSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊)) • x ∈ D.PSZ p (r := r)) ∧
      (∀ x ∈ D.PSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊)) • x ∈ D.SSZ p (r := r))
def FockBlocks : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → 1 ≤ r →
    (∀ (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ), D.LevelOK j jp → D.LevelOK j' jp' → (j, jp) ≠ (j', jp') →
      ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∀ y' ∈ Y p (r := r) (D.lettersAt j' jp') D.T.J D.T.thr,
      ∀ g ∈ XiPolZ p N r D.T.t (D.B - jp), ∀ g' ∈ XiPolZ p N r D.T.t (D.B - jp'),
        fockK ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
            D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g))
          ((∏ i, D.Ehat p (r := r) i ^ j' i) * D.Eplus p (r := r) ^ jp' *
            D.Pall p (r := r) j' jp' (rename (chainEmb N r D.T.t) y' * g')) = 0) ∧
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp →
      ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∀ y' ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      ∀ g ∈ XiPolZ p N r D.T.t (D.B - jp), ∀ g' ∈ XiPolZ p N r D.T.t (D.B - jp),
        fockK ((((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p]))⁻¹) •
            ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
              D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g)))
          ((((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p]))⁻¹) •
            ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
              D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y' * g'))) =
          (∏ i, ((((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) +
                (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) + r + D.T.z i + 1 + j i - 1).choose (j i) *
              (D.T.z i).factorial : ℕ) : ℚ_[p])) *
            ((((D.LL.deg D.uPos - jp) + (D.B - jp) + r + D.zPlus + 1 + jp - 1).choose jp *
              D.zPlus.factorial : ℕ) : ℚ_[p]) *
            fockK (rename (chainEmb N r D.T.t) y * g)
              (D.phiAll p (r := r) j jp (rename (chainEmb N r D.T.t) y' * g')))
end Formalism.GM.M


