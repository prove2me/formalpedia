-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:54.73893+00:00
-- url     : https://prove2.me/theorems/ec5d34cf-81ae-417f-b43a-f9aa9954622a
-- title:
--   Pair Step
-- statement:
--   Definitions and structural lemmas for Pair Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PairStep.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
def PairStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ) (zv sv : σ), 1 ≤ r → (∀ c, w c ≠ zv ∧ e c ≠ zv) →
    ∀ (o n z L u : ℕ) (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])),
      (∀ l, ∀ x ∈ Λ l, ∀ m, min (o - l) (n - l) < m → (tieF w e ^ m) x = 0) →
      (∀ l m, m ≤ min o n → ∀ x ∈ Λ l,
        (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) x) ∈ Λ (l + m)) →
      r * L + Nat.log p (o + n + r + z) ≤ u →
      ∀ l ≤ min o n, ∀ x ∈ Λ l,
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * (X zv ^ z * x)) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * tieP w e zv sv (o - l') (n - l') z x'}) ∧
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * tieP w e zv sv (o - l) (n - l) z x) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * (X zv ^ z * x')})
section block
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
def HypJoin : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
      Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr
def HypU : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr
noncomputable def midGen (k : ℕ) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x
noncomputable def Mid (k : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = midGen p D k j jp x}
noncomputable def MidP : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)}
end block
def LatPlus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypU p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wU D) (xiVar N r D.T.t) ^ m) x) ∈
        Lat p D (r := r) j (jp + m)
def LatTie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypJoin p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wv D i) (ev D i) ^ m) x) ∈
        Lat p D (r := r) (j + Pi.single i m) jp
def PLLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ),
    (∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = PL p D L j jp x) ∧
    ∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = Pplus p D jp x
def CommPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp m : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ k : Fin D.T.t, k ∉ L →
        (tieF (wv D k) (ev D k) ^ m) (PL p D L j jp x) = PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x)) ∧
      (tieF (wU D) (xiVar N r D.T.t) ^ m) (PL p D L j jp x) =
        PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x)
def ParamPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ i ∈ L, j i = j' i) → PL p D L j jp x = PL p D L j' jp' x
def MidTop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), Mid p (r := r) D D.T.t = D.SSZ p (r := r)
def MidPEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), MidP p (r := r) D = D.PSZ p (r := r)
def JoinCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → (∀ i, D.T.z i ≤ 2 * a) → HypJoin p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u → ∀ k < D.T.t,
      (∀ v ∈ Mid p (r := r) D (k + 1), (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k) ∧
      (∀ v ∈ Mid p (r := r) D k, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D (k + 1))
def PlusCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → D.zPlus ≤ 2 * a → HypU p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u →
      (∀ v ∈ Mid p (r := r) D 0, (p : ℚ_[p]) ^ u • v ∈ MidP p (r := r) D) ∧
      (∀ v ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D 0)
end Formalism.InvariantFactorPaths.KP.LL


