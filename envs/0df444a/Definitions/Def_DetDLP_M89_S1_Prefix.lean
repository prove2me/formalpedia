-- Prove2me | Definitions.Def_DetDLP_M89_S1_Prefix
-- name    : DetDLP_M89_S1_Prefix
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:00:46.444446+00:00
-- url     : https://prove2.me/theorems/b8036e1c-0ecf-4036-8c9e-590442d814f8
-- title:
--   Fixed-width seed words and the winning prefix slice
-- statement:
--   List the slope and offset words in block order, most significant bit first. Starting with all valid seeds, retain the nonempty child of smaller conditional mean, with a left tie break. The final slice specifies the same affine blocks for the enumerator and the decoder. In the small regime the specified blocks are the whole group.
-- source:
--   Deterministic Discrete Logarithms in Subexponential Time from Boolean Tensor Contraction, Sections 3.1–3.2, proof of Theorem 3.1, equation (3.5).

import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_M89_SeedSelection

set_option autoImplicit false
namespace DetDLP.M89S1

/-- Read coordinate words in block-major order, each most significant bit first. -/
def packBits {m t b : ℕ} (w : Fin m → Fin t → ℕ) (j : Fin ((m*t)*b)) : Bool :=
  let u := finProdFinEquiv.symm j
  let v := finProdFinEquiv.symm u.1
  (w v.1 v.2).testBit u.2.rev.val

def fpWords {p m : ℕ} (S : FpSeed p m) (i : Fin m) (k : Fin 2) : ℕ :=
  if k = 0 then (S i).1.val+1 else (S i).2.val

def ecWords {p m : ℕ} (S : ECSeed p m) (i : Fin m) (k : Fin 4) : ℕ :=
  let ab := S i (decide (2 ≤ k.val))
  if k.val % 2 = 0 then ab.1.val+1 else ab.2.val

abbrev fpBits {p m : ℕ} (S : FpSeed p m) := packBits (b := bitLen p) (fpWords S)
abbrev ecBits {p m : ℕ} (S : ECSeed p m) := packBits (b := bitLen p) (ecWords S)

abbrev Node (α : Type) := ℕ × Finset α

def child {α : Type} {L : ℕ} (bits : α → Fin L → Bool) (a : Node α) (v : Bool) : Node α :=
  (a.1+1, if h : a.1 < L then a.2.filter (fun s => bits s ⟨a.1,h⟩ = v) else ∅)

/-- The nonempty slice selected by comparing the two conditional means; ties go left. -/
noncomputable def winners {α : Type} [Fintype α] {L : ℕ} (bits : α → Fin L → Bool)
    (f : α → ℝ) : Finset α :=
  (M89SeedSelection.descend (fun a : Node α => a.2.card) (fun a => ∑ s ∈ a.2, f s)
    (child bits) L (0,Finset.univ)).2

noncomputable def fpCost (p m : ℕ) [Fact p.Prime] (S : FpSeed p m) : ℝ :=
  let T := hashThreshold p (p-1) m (p-1)
  collisionPotentialMul ((qBlk p (p-1) T)^m) (fpFactorBlock (p := p) T S)

noncomputable def ecCost {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    {m : ℕ} (S : ECSeed p m) : ℝ :=
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  let T := hashThreshold p (g-1) m g
  collisionPotentialAdd ((qBlk p (g-1) T)^m) (ecFactorBlock E T S)

/-- The two machines agree on the small branch and on the exact winning prefix in the large branch. -/
def fpBase {p m : ℕ} [Fact p.Prime] (D : Fin m → Finset (ZMod p)ˣ) : Prop :=
  (¬ (64 ≤ p-1 ∧ 4096*m ≤ p-1) ∧ ∀ i, D i = Finset.univ) ∨
  (64 ≤ p-1 ∧ 4096*m ≤ p-1 ∧ ∃ S ∈ winners fpBits (fpCost p m),
    ∀ i, D i = fpFactorBlock (p := p) (hashThreshold p (p-1) m (p-1)) S i)

def ecBase {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (D : Fin m → Finset E.toAffine.Point) : Prop :=
  letI := ecPointFintype E
  let g := Fintype.card E.toAffine.Point
  (¬ (64 ≤ g ∧ 4096*m ≤ g-1) ∧ ∀ i, D i = Finset.univ) ∨
  (64 ≤ g ∧ 4096*m ≤ g-1 ∧ ∃ S ∈ winners ecBits (ecCost E (m := m)),
    ∀ i, D i = ecFactorBlock E (hashThreshold p (g-1) m g) S i)

end DetDLP.M89S1


