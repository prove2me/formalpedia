-- Prove2me | Definitions.Def_DetDLP_W4_M5GraphBounds
-- name    : DetDLP_W4_M5GraphBounds
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:36:17.03239+00:00
-- url     : https://prove2.me/theorems/a61c2f62-7df2-4308-b321-f06d4091a1a0
-- title:
--   The two-layer multiplication graph and its size bounds
-- statement:
--   Defines an explicit numbering of gates and edges, and proves the strict edge and maximum-degree bounds of Lemma 2.3.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5MixedNetwork
import Definitions.Def_DetDLP_W4_M5Parameters

set_option autoImplicit false

namespace DetDLP.w4_M5GraphBounds
open DetDLP.w4_MulParams DetDLP.w4_M5Network

/- The type-level constructors match the two-layer circuit. The ten classes use
explicit contiguous indices. No arbitrary enumeration of gates is needed. -/

inductive Vertex (d : ℕ) where
  | inputBit (x0 : Fin 2) (x1 : Fin d)
  | pack (x0 : Fin 2) (x1 : Fin (n0 d))
  | forward1 (x0 : Fin 2) (x1 : Fin (L2 d))
  | forward2 (x0 : Fin 2) (x1 : Fin (L1 d))
  | pointwise (x0 : Fin (L2 d)) (x1 : Fin (L1 d))
  | inverse1 (x0 : Fin (L1 d))
  | inverse2 (x0 : Fin (L2 d))
  | carry (x0 : Fin (2 * n0 d))
  | carrySpacer (x0 : Fin (2 * n0 d - 1))
  | outputBit (x0 : Fin (2 * d))
  deriving DecidableEq

private abbrev vertexCode (d : ℕ) :=
  (Fin 2 × Fin d) ⊕
  (Fin 2 × Fin (n0 d)) ⊕
  (Fin 2 × Fin (L2 d)) ⊕
  (Fin 2 × Fin (L1 d)) ⊕
  (Fin (L2 d) × Fin (L1 d)) ⊕
  (Fin (L1 d)) ⊕
  (Fin (L2 d)) ⊕
  (Fin (2 * n0 d)) ⊕
  (Fin (2 * n0 d - 1)) ⊕
  (Fin (2 * d))

def vertexCount (d : ℕ) : ℕ :=
  ((2 * d) + ((2 * (n0 d)) + ((2 * (L2 d)) + ((2 * (L1 d)) + (((L2 d) * (L1 d)) + ((L1 d) + ((L2 d) + ((2 * n0 d) + ((2 * n0 d - 1) + (2 * d))))))))))

private def vertexToCode {d : ℕ} : Vertex d → vertexCode d
  | .inputBit x0 x1 => (.inl (x0, x1))
  | .pack x0 x1 => (.inr (.inl (x0, x1)))
  | .forward1 x0 x1 => (.inr (.inr (.inl (x0, x1))))
  | .forward2 x0 x1 => (.inr (.inr (.inr (.inl (x0, x1)))))
  | .pointwise x0 x1 => (.inr (.inr (.inr (.inr (.inl (x0, x1))))))
  | .inverse1 x0 => (.inr (.inr (.inr (.inr (.inr (.inl (x0)))))))
  | .inverse2 x0 => (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0))))))))
  | .carry x0 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0)))))))))
  | .carrySpacer x0 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0))))))))))
  | .outputBit x0 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x0))))))))))

private def vertexFromCode {d : ℕ} : vertexCode d → Vertex d
  | (.inl (x0, x1)) => .inputBit x0 x1
  | (.inr (.inl (x0, x1))) => .pack x0 x1
  | (.inr (.inr (.inl (x0, x1)))) => .forward1 x0 x1
  | (.inr (.inr (.inr (.inl (x0, x1))))) => .forward2 x0 x1
  | (.inr (.inr (.inr (.inr (.inl (x0, x1)))))) => .pointwise x0 x1
  | (.inr (.inr (.inr (.inr (.inr (.inl (x0))))))) => .inverse1 x0
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0)))))))) => .inverse2 x0
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0))))))))) => .carry x0
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0)))))))))) => .carrySpacer x0
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x0)))))))))) => .outputBit x0

private def vertexTagEquiv (d : ℕ) : Vertex d ≃ vertexCode d where
  toFun := vertexToCode
  invFun := vertexFromCode
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨x0, x1⟩ | ⟨x0, x1⟩ | ⟨x0, x1⟩ | ⟨x0, x1⟩ | ⟨x0, x1⟩ | x | x | x | x | x <;> rfl

/-- Contiguous computable numbering of the vertex classes. -/
def vertexIndex (d : ℕ) : Vertex d ≃ Fin (vertexCount d) :=
  (vertexTagEquiv d).trans
    ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin d))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin (n0 d)))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin (L2 d)))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin (L1 d)))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (L2 d))) (Equiv.refl (Fin (L1 d)))).trans finProdFinEquiv) ((Equiv.sumCongr (Equiv.refl (Fin (L1 d))) ((Equiv.sumCongr (Equiv.refl (Fin (L2 d))) ((Equiv.sumCongr (Equiv.refl (Fin (2 * n0 d))) ((Equiv.sumCongr (Equiv.refl (Fin (2 * n0 d - 1))) (Equiv.refl (Fin (2 * d)))).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)

inductive Edge (d t : ℕ) where
  | input (x0 : Fin 2) (x1 : Fin d)
  | packForward (x0 : Fin 2) (x1 : Fin (n0 d)) (x2 : Fin t)
  | forwardMiddle (x0 : Fin 2) (x1 : Fin (L2 d)) (x2 : Fin (L1 d)) (x3 : Fin t)
  | forwardPoint (x0 : Fin 2) (x1 : Fin (L2 d)) (x2 : Fin (L1 d)) (x3 : Fin t)
  | pointInverse (x0 : Fin (L2 d)) (x1 : Fin (L1 d)) (x2 : Fin t)
  | inverseMiddle (x0 : Fin (L2 d)) (x1 : Fin (L1 d)) (x2 : Fin t)
  | coefficient (x0 : Fin (2 * n0 d)) (x1 : Fin t)
  | carryLeft (x0 : Fin (2 * n0 d - 1)) (x1 : Fin t)
  | carryRight (x0 : Fin (2 * n0 d - 1)) (x1 : Fin t)
  | output (x0 : Fin (2 * d))
  deriving DecidableEq

private abbrev edgeCode (d t : ℕ) :=
  (Fin 2 × Fin d) ⊕
  (Fin 2 × Fin (n0 d) × Fin t) ⊕
  (Fin 2 × Fin (L2 d) × Fin (L1 d) × Fin t) ⊕
  (Fin 2 × Fin (L2 d) × Fin (L1 d) × Fin t) ⊕
  (Fin (L2 d) × Fin (L1 d) × Fin t) ⊕
  (Fin (L2 d) × Fin (L1 d) × Fin t) ⊕
  (Fin (2 * n0 d) × Fin t) ⊕
  (Fin (2 * n0 d - 1) × Fin t) ⊕
  (Fin (2 * n0 d - 1) × Fin t) ⊕
  (Fin (2 * d))

def edgeCount (d t : ℕ) : ℕ :=
  ((2 * d) + ((2 * ((n0 d) * t)) + ((2 * ((L2 d) * ((L1 d) * t))) + ((2 * ((L2 d) * ((L1 d) * t))) + (((L2 d) * ((L1 d) * t)) + (((L2 d) * ((L1 d) * t)) + (((2 * n0 d) * t) + (((2 * n0 d - 1) * t) + (((2 * n0 d - 1) * t) + (2 * d))))))))))

private def edgeToCode {d t : ℕ} : Edge d t → edgeCode d t
  | .input x0 x1 => (.inl (x0, x1))
  | .packForward x0 x1 x2 => (.inr (.inl (x0, x1, x2)))
  | .forwardMiddle x0 x1 x2 x3 => (.inr (.inr (.inl (x0, x1, x2, x3))))
  | .forwardPoint x0 x1 x2 x3 => (.inr (.inr (.inr (.inl (x0, x1, x2, x3)))))
  | .pointInverse x0 x1 x2 => (.inr (.inr (.inr (.inr (.inl (x0, x1, x2))))))
  | .inverseMiddle x0 x1 x2 => (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1, x2)))))))
  | .coefficient x0 x1 => (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1))))))))
  | .carryLeft x0 x1 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1)))))))))
  | .carryRight x0 x1 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1))))))))))
  | .output x0 => (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x0))))))))))

private def edgeFromCode {d t : ℕ} : edgeCode d t → Edge d t
  | (.inl (x0, x1)) => .input x0 x1
  | (.inr (.inl (x0, x1, x2))) => .packForward x0 x1 x2
  | (.inr (.inr (.inl (x0, x1, x2, x3)))) => .forwardMiddle x0 x1 x2 x3
  | (.inr (.inr (.inr (.inl (x0, x1, x2, x3))))) => .forwardPoint x0 x1 x2 x3
  | (.inr (.inr (.inr (.inr (.inl (x0, x1, x2)))))) => .pointInverse x0 x1 x2
  | (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1, x2))))))) => .inverseMiddle x0 x1 x2
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1)))))))) => .coefficient x0 x1
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1))))))))) => .carryLeft x0 x1
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x0, x1)))))))))) => .carryRight x0 x1
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x0)))))))))) => .output x0

private def edgeTagEquiv (d t : ℕ) : Edge d t ≃ edgeCode d t where
  toFun := edgeToCode
  invFun := edgeFromCode
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨x0, x1⟩ | ⟨x0, x1, x2⟩ | ⟨x0, x1, x2, x3⟩ | ⟨x0, x1, x2, x3⟩ | ⟨x0, x1, x2⟩ | ⟨x0, x1, x2⟩ | ⟨x0, x1⟩ | ⟨x0, x1⟩ | ⟨x0, x1⟩ | x <;> rfl

/-- Contiguous computable numbering of the edge classes. -/
def edgeIndex (d t : ℕ) : Edge d t ≃ Fin (edgeCount d t) :=
  (edgeTagEquiv d t).trans
    ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.refl (Fin d))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) ((Equiv.prodCongr (Equiv.refl (Fin (n0 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv)).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) ((Equiv.prodCongr (Equiv.refl (Fin (L2 d))) ((Equiv.prodCongr (Equiv.refl (Fin (L1 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv)).trans finProdFinEquiv)).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin 2)) ((Equiv.prodCongr (Equiv.refl (Fin (L2 d))) ((Equiv.prodCongr (Equiv.refl (Fin (L1 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv)).trans finProdFinEquiv)).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (L2 d))) ((Equiv.prodCongr (Equiv.refl (Fin (L1 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv)).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (L2 d))) ((Equiv.prodCongr (Equiv.refl (Fin (L1 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv)).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (2 * n0 d))) (Equiv.refl (Fin t))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (2 * n0 d - 1))) (Equiv.refl (Fin t))).trans finProdFinEquiv) ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin (2 * n0 d - 1))) (Equiv.refl (Fin t))).trans finProdFinEquiv) (Equiv.refl (Fin (2 * d)))).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)

/-- Internal words use `J+1` bits. External input and output edges are single bits. -/
abbrev W (d : ℕ) := J d + 1

private theorem n0_pos' {d : ℕ} (hd : 1 ≤ d) : 0 < n0 d := n0_pos hd

/-- Exact arithmetic counts; `2*n0-1` equality vertices are included. -/
theorem vertexCount_eq {d : ℕ} (hd : 1 ≤ d) :
    vertexCount d = 4*d + 6*n0 d + 3*L1 d + 3*L2 d + L d - 1 := by
  have hp := n0_pos hd
  have hLL : L2 d * L1 d = L d := (Nat.mul_comm ..).trans (L1_mul_L2 d)
  unfold vertexCount
  rw [hLL]
  omega

theorem edgeCount_eq {d : ℕ} (hd : 1 ≤ d) (t : ℕ) :
    edgeCount d t = 4*d + (6*L d + 8*n0 d - 2)*t := by
  have hp := n0_pos hd
  have hLL : L2 d * L1 d = L d := (Nat.mul_comm ..).trans (L1_mul_L2 d)
  have h1 : 2*n0 d - 1 + 1 = 2*n0 d := by omega
  have h2 : 6*L d + 8*n0 d - 2 + 2 = 6*L d + 8*n0 d := by omega
  unfold edgeCount
  rw [← Nat.mul_assoc (L2 d), hLL]
  nlinarith only [congrArg (· * t) h1, congrArg (· * t) h2]

private theorem kpos {d : ℕ} (hd : 1 ≤ d) : 0 < k d := by have := k_ge_four hd; omega

def inLimb {d : ℕ} (hd : 1 ≤ d) (i : Fin d) : Fin (n0 d) :=
  ⟨i.val / k d, (Nat.div_lt_iff_lt_mul (kpos hd)).mpr
    (by have h := n0_covers hd; rw [mul_comm] at h; exact i.isLt.trans_le h)⟩

def outLimb {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d)) : Fin (2*n0 d) :=
  ⟨i.val / k d, (Nat.div_lt_iff_lt_mul (kpos hd)).mpr
    (by have h := Nat.mul_le_mul_left 2 (n0_covers hd)
        rw [mul_comm (k d), ← mul_assoc] at h
        exact i.isLt.trans_le h)⟩

/-- Fourier first blocks have fixed `j₂`; physical input index is `L₂*j₁+j₂`. -/
def column {d : ℕ} (i : ℕ) : Fin (L2 d) := ⟨i % L2 d, Nat.mod_lt _ (L2_pos d)⟩

def carryHead {d : ℕ} (i : Fin (2*n0 d - 1)) : Fin (2*n0 d) := ⟨i.val, by omega⟩

def carryTail {d : ℕ} (i : Fin (2*n0 d - 1)) : Fin (2*n0 d) := ⟨i.val+1, by omega⟩

def src {d t : ℕ} (hd : 1 ≤ d) : Edge d t → Vertex d
  | .input a i => .inputBit a i
  | .packForward a i _ => .pack a i
  | .forwardMiddle a b _ _ => .forward1 a b
  | .forwardPoint a _ j _ => .forward2 a j
  | .pointInverse b j _ => .pointwise b j
  | .inverseMiddle _ j _ => .inverse1 j
  | .coefficient i _ => .inverse2 (column i.val)
  | .carryLeft i _ => .carry (carryHead i)
  | .carryRight i _ => .carrySpacer i
  | .output i => .carry (outLimb hd i)

def dst {d t : ℕ} (hd : 1 ≤ d) : Edge d t → Vertex d
  | .input a i => .pack a (inLimb hd i)
  | .packForward a i _ => .forward1 a (column i.val)
  | .forwardMiddle a _ j _ => .forward2 a j
  | .forwardPoint _ b j _ => .pointwise b j
  | .pointInverse _ j _ => .inverse1 j
  | .inverseMiddle b _ _ => .inverse2 b
  | .coefficient i _ => .carry i
  | .carryLeft i _ => .carrySpacer i
  | .carryRight i _ => .carry (carryTail i)
  | .output i => .outputBit i

def side {d : ℕ} : Vertex d → Bool
  | .inputBit .. | .forward1 .. | .pointwise .. | .inverse2 .. | .carrySpacer .. | .outputBit .. => true
  | _ => false

theorem opposite {d t : ℕ} (hd : 1 ≤ d) (e : Edge d t) : side (src hd e) ≠ side (dst hd e) := by
  cases e <;> simp [side, src, dst]

/-- The final graph including all individual bits of every transform and carry word. -/
def graph (d : ℕ) (hd : 1 ≤ d) : BipartiteMultigraph where
  nV := vertexCount d
  nE := edgeCount d (W d)
  endpoints i := let e := (edgeIndex d (W d)).symm i
                 (vertexIndex d (src hd e), vertexIndex d (dst hd e))
  side i := side ((vertexIndex d).symm i)
  bipartite i := by
    simp only [Equiv.symm_apply_apply]
    apply opposite

theorem graph_nE {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nE = 4*d + (6*L d + 8*n0 d - 2)*(J d + 1) :=
  edgeCount_eq hd _

theorem graph_nV {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nV = 4*d + 6*n0 d + 3*L1 d + 3*L2 d + L d - 1 :=
  vertexCount_eq hd

theorem graph_edge_bound {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nE < 1100 * (d+1) := by
  have hL := L_le_half_J hd
  have hn := n0_upper hd
  have hsum : 6*L d + 8*n0 d - 2 ≤ 4*J d := by omega
  rw [graph_nE hd]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hsum) _).trans_lt (size_bounds hd).2.2.1

theorem graph_vertex_bound {d : ℕ} (hd : 1 ≤ d) : ((graph d hd).nV : ℝ) ≤ polyBound 256 d := by
  have hJ := J_lt_linear hd
  have hn := n0_upper hd
  have hL := L_le_half_J hd
  have hr := L1_le_L d
  have hc := L2_le_L d
  have hV : (graph d hd).nV ≤ 256*(d+1) := by rw [graph_nV hd]; omega
  have hbase : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hpow := pow_le_pow_right₀ hbase (by decide : 1 ≤ 256)
  have hvR : ((graph d hd).nV : ℝ) ≤ 256*((d : ℝ)+1) := by exact_mod_cast hV
  unfold polyBound
  push_cast
  exact hvR.trans (mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hpow) (by norm_num))

private theorem two_le_L2 {d : ℕ} (hd : 1 ≤ d) : 2 ≤ L2 d := by
  have hm := mu_pos hd
  unfold L2
  exact (show 2^1 ≤ 2^((μ d+1)/2) from Nat.pow_le_pow_right (by decide) (by omega))

private theorem k_le_W {d : ℕ} (hd : 1 ≤ d) : k d ≤ W d := by
  change k d ≤ J d + 1
  have h := four_mul_k hd
  omega

/-- A local word slot is the pair (word port, bit index), with the bit varying fastest. -/
def block {t : ℕ} (a : ℕ) (r : Fin t) : ℕ := r.val + t * a

@[simp] theorem block_inj {t a b : ℕ} {r s : Fin t} : block a r = block b s ↔ a = b ∧ r = s := by
  constructor
  · intro h
    have ht : 0 < t := Nat.zero_lt_of_lt r.isLt
    have ha := congrArg (· / t) h
    have hr := congrArg (· % t) h
    dsimp [block] at ha hr
    simp only [Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt r.isLt,
      Nat.div_eq_of_lt s.isLt, zero_add] at ha
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] at hr
    exact ⟨ha, Fin.ext hr⟩
  · rintro ⟨rfl,rfl⟩; rfl

private theorem block_lt {t a B : ℕ} (ha : a < B) (r : Fin t) : block a r < B*t := by
  have h := Nat.mul_le_mul_right t (show a + 1 ≤ B from ha)
  dsimp [block]
  rw [Nat.add_one_mul] at h
  rw [Nat.mul_comm t]
  omega

private theorem eq_of_div_mod {a b k : ℕ} (hdiv : a/k = b/k) (hmod : a%k = b%k) : a = b := by
  rw [← Nat.mod_add_div a k, hdiv, hmod, Nat.mod_add_div]

private theorem row_lt {d : ℕ} {n : ℕ} (h : n < L d) : n / L2 d < L1 d := by
  apply (Nat.div_lt_iff_lt_mul (L2_pos d)).mpr
  rwa [L1_mul_L2]

/-- Outgoing slots reserve a separate block for a carry vertex's output bits. -/
def outSlot {d : ℕ} : Edge d (W d) → ℕ
  | .input .. => 0
  | .packForward _ _ r => r.val
  | .forwardMiddle _ _ j r => block j.val r
  | .forwardPoint _ b _ r => block b.val r
  | .pointInverse _ _ r => r.val
  | .inverseMiddle b _ r => block b.val r
  | .coefficient i r => block (i.val / L2 d) r
  | .carryLeft _ r => r.val
  | .carryRight _ r => r.val
  | .output i => W d + i.val % k d

/-- Incoming slots reserve the high block at a carry vertex for the previous carry. -/
def inSlot {d : ℕ} : Edge d (W d) → ℕ
  | .input _ i => i.val % k d
  | .packForward _ i r => block (i.val / L2 d) r
  | .forwardMiddle _ b _ r => block b.val r
  | .forwardPoint a _ _ r => block a.val r
  | .pointInverse b _ r => block b.val r
  | .inverseMiddle _ j r => block j.val r
  | .coefficient _ r => r.val
  | .carryLeft _ r => r.val
  | .carryRight _ r => W d + r.val
  | .output _ => 0

theorem outSlot_lt {d : ℕ} (hd : 1 ≤ d) (e : Edge d (W d)) : outSlot e < L2 d * W d := by
  have h2 := two_le_L2 hd
  have h2w : 2*W d ≤ L2 d * W d := Nat.mul_le_mul_right _ h2
  have hr := L1_le_L2 d
  have hk := kpos hd
  have hkw := k_le_W hd
  have hcap := L_lower hd
  cases e with
  | input a i => exact Nat.mul_pos (L2_pos d) (Nat.succ_pos _)
  | packForward a i r => exact lt_of_lt_of_le r.isLt (by omega)
  | forwardMiddle a b j r => exact block_lt (j.isLt.trans_le hr) r
  | forwardPoint a b j r => exact block_lt b.isLt r
  | pointInverse b j r => exact lt_of_lt_of_le r.isLt (by omega)
  | inverseMiddle b j r => exact block_lt b.isLt r
  | coefficient i r => exact block_lt ((row_lt (i.isLt.trans_le hcap)).trans_le hr) r
  | carryLeft i r => exact lt_of_lt_of_le r.isLt (by omega)
  | carryRight i r => exact lt_of_lt_of_le r.isLt (by omega)
  | output i => simp only [outSlot]; have := Nat.mod_lt i.val hk; omega

theorem inSlot_lt {d : ℕ} (hd : 1 ≤ d) (e : Edge d (W d)) : inSlot e < L2 d * W d := by
  have h2 := two_le_L2 hd
  have h2w : 2*W d ≤ L2 d * W d := Nat.mul_le_mul_right _ h2
  have hr := L1_le_L2 d
  have hk := kpos hd
  have hkw := k_le_W hd
  have hcap := L_lower hd
  cases e with
  | input a i => simp only [inSlot]; have := Nat.mod_lt i.val hk; omega
  | packForward a i r => exact block_lt ((row_lt (show i.val < L d by omega)).trans_le hr) r
  | forwardMiddle a b j r => exact block_lt b.isLt r
  | forwardPoint a b j r => exact block_lt (a.isLt.trans_le h2) r
  | pointInverse b j r => exact block_lt b.isLt r
  | inverseMiddle b j r => exact block_lt (j.isLt.trans_le hr) r
  | coefficient i r => exact lt_of_lt_of_le r.isLt (by omega)
  | carryLeft i r => exact lt_of_lt_of_le r.isLt (by omega)
  | carryRight i r => simp only [inSlot]; omega
  | output i => exact Nat.mul_pos (L2_pos d) (Nat.succ_pos _)

@[simp] private theorem block_div {t} (a : ℕ) (r : Fin t) : block a r / t = a := by
  rw [block, Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt r.isLt), Nat.div_eq_of_lt r.isLt, zero_add]

@[simp] private theorem block_mod {t} (a : ℕ) (r : Fin t) : block a r % t = r.val := by
  rw [block, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]

private def checked (n x : ℕ) : Option (Fin n) := if h : x < n then some ⟨x,h⟩ else none

@[simp] private theorem checked_val {n} (x : Fin n) : checked n x.val = some x := by
  simp [checked,x.isLt]

private def readOut {d : ℕ} (v : Vertex d) (s : ℕ) : Option (Edge d (W d)) := do
  match v with
  | .inputBit a i => return .input a i
  | .pack a i => return .packForward a i (← checked _ s)
  | .forward1 a b => return .forwardMiddle a b (← checked _ (s / W d)) (← checked _ (s % W d))
  | .forward2 a j => return .forwardPoint a (← checked _ (s / W d)) j (← checked _ (s % W d))
  | .pointwise b j => return .pointInverse b j (← checked _ s)
  | .inverse1 j => return .inverseMiddle (← checked _ (s / W d)) j (← checked _ (s % W d))
  | .inverse2 b => return .coefficient (← checked _ (b.val + L2 d * (s / W d))) (← checked _ (s % W d))
  | .carry i => if s < W d then return .carryLeft (← checked _ i.val) (← checked _ s)
                else return .output (← checked _ ((s - W d) + k d * i.val))
  | .carrySpacer i => return .carryRight i (← checked _ s)
  | .outputBit _ => none

private def readIn {d : ℕ} (v : Vertex d) (s : ℕ) : Option (Edge d (W d)) := do
  match v with
  | .inputBit _ _ => none
  | .pack a i => return .input a (← checked _ (s + k d * i.val))
  | .forward1 a b => return .packForward a (← checked _ (b.val + L2 d * (s / W d))) (← checked _ (s % W d))
  | .forward2 a j => return .forwardMiddle a (← checked _ (s / W d)) j (← checked _ (s % W d))
  | .pointwise b j => return .forwardPoint (← checked _ (s / W d)) b j (← checked _ (s % W d))
  | .inverse1 j => return .pointInverse (← checked _ (s / W d)) j (← checked _ (s % W d))
  | .inverse2 b => return .inverseMiddle b (← checked _ (s / W d)) (← checked _ (s % W d))
  | .carry i => if s < W d then return .coefficient i (← checked _ s)
                else return .carryRight (← checked _ (i.val-1)) (← checked _ (s-W d))
  | .carrySpacer i => return .carryLeft i (← checked _ s)
  | .outputBit i => return .output i

private theorem readOut_out {d : ℕ} (hd : 1 ≤ d) (e : Edge d (W d)) :
    readOut (src hd e) (outSlot e) = some e := by
  cases e <;> simp [src, outSlot, readOut, column, outLimb, carryHead, Nat.mod_add_div]
  · rename_i i r
    have h : r.val < J d+1 := r.isLt
    omega
  · unfold W
    omega

private theorem readIn_in {d : ℕ} (hd : 1 ≤ d) (e : Edge d (W d)) :
    readIn (dst hd e) (inSlot e) = some e := by
  cases e <;> simp [dst, inSlot, readIn, column, inLimb, carryTail, Nat.mod_add_div]
  · rename_i i r
    have h : r.val < J d+1 := r.isLt
    omega
  · unfold W
    omega

theorem outSlot_injective {d : ℕ} (hd : 1 ≤ d) {e f : Edge d (W d)}
    (hv : src hd e = src hd f) (hs : outSlot e = outSlot f) : e = f := by
  have h := readOut_out hd e
  rw [hv, hs, readOut_out] at h
  exact (Option.some.inj h).symm

theorem inSlot_injective {d : ℕ} (hd : 1 ≤ d) {e f : Edge d (W d)}
    (hv : dst hd e = dst hd f) (hs : inSlot e = inSlot f) : e = f := by
  have h := readIn_in hd e
  rw [hv, hs, readIn_in] at h
  exact (Option.some.inj h).symm

/-- Assign each actual ordered edge port a direction tag and a local slot. -/
private def codeAt {d : ℕ} (hd : 1 ≤ d) (v : Vertex d) (e : Edge d (W d)) :
    Fin (L2 d*W d) ⊕ Fin (L2 d*W d) :=
  if src hd e = v then .inl ⟨outSlot e,outSlot_lt hd e⟩
  else .inr ⟨inSlot e,inSlot_lt hd e⟩

private theorem codeAt_inj {d : ℕ} (hd : 1 ≤ d) {v : Vertex d} {e f : Edge d (W d)}
    (he : src hd e = v ∨ dst hd e = v) (hf : src hd f = v ∨ dst hd f = v)
    (h : codeAt hd v e = codeAt hd v f) : e = f := by
  by_cases hse : src hd e = v <;> by_cases hsf : src hd f = v
  · apply outSlot_injective hd (hse.trans hsf.symm)
    exact congrArg Fin.val (Sum.inl.inj (by simpa only [codeAt, if_pos hse, if_pos hsf] using h))
  · simp only [codeAt, if_pos hse, if_neg hsf, reduceCtorEq] at h
  · simp only [codeAt, if_neg hse, if_pos hsf, reduceCtorEq] at h
  · apply inSlot_injective hd ((he.resolve_left hse).trans (hf.resolve_left hsf).symm)
    exact congrArg Fin.val (Sum.inr.inj (by simpa only [codeAt, if_neg hse, if_neg hsf] using h))

private def incidentEdge {d : ℕ} (hd : 1 ≤ d) (v : Fin (vertexCount d))
    (i : Fin ((graph d hd).deg v)) : Edge d (W d) :=
  (edgeIndex d (W d)).symm (((graph d hd).ports v).get i)

private theorem getPort_incident (G : BipartiteMultigraph) (v : Fin G.nV)
    (i : Fin (G.deg v)) :
    (G.endpoints ((G.ports v).get i)).1 = v ∨ (G.endpoints ((G.ports v).get i)).2 = v :=
  of_decide_eq_true (List.mem_filter.mp (List.get_mem (G.ports v) i)).2

private theorem incidentEdge_spec {d : ℕ} (hd : 1 ≤ d) (v : Fin (vertexCount d))
    (i : Fin ((graph d hd).deg v)) :
    src hd (incidentEdge hd v i) = (vertexIndex d).symm v ∨
      dst hd (incidentEdge hd v i) = (vertexIndex d).symm v := by
  rcases getPort_incident (graph d hd) v i with h | h
  · left; exact (vertexIndex d).apply_eq_iff_eq_symm_apply.mp h
  · right; exact (vertexIndex d).apply_eq_iff_eq_symm_apply.mp h

/-- Per-vertex bit degree, on the actual ordered ports of the compiled graph. -/
theorem graph_degree_bound {d : ℕ} (hd : 1 ≤ d) (v : Fin (vertexCount d)) :
    (graph d hd).deg v ≤ 2 * L2 d * (J d+1) := by
  let code (i : Fin ((graph d hd).deg v)) :=
    codeAt hd ((vertexIndex d).symm v) (incidentEdge hd v i)
  have hinj : Function.Injective code := by
    intro i j hij
    have h := codeAt_inj hd (incidentEdge_spec hd v i) (incidentEdge_spec hd v j) hij
    have hget := (edgeIndex d (W d)).symm.injective h
    have hn : ((graph d hd).ports v).Nodup := (List.nodup_finRange _).filter _
    exact hn.get_inj_iff.mp hget
  have h := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  simpa only [two_mul, Nat.add_mul] using h

theorem graph_maxDeg_bound {d : ℕ} (hd : 1 ≤ d) :
    ((graph d hd).maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  have h : (graph d hd).maxDeg ≤ 2 * L2 d * (J d+1) :=
    Finset.sup_le (fun v _ => graph_degree_bound hd v)
  have hR : ((graph d hd).maxDeg : ℝ) ≤ 2 * (L2 d : ℝ) * ((J d : ℝ)+1) := by exact_mod_cast h
  exact hR.trans_lt (by simpa only [max_eq_right (L1_le_L2 d)] using (size_bounds hd).2.2.2)

/-- All three quantitative graph obligations of Lemma 2.3. -/
theorem graph_bounds {d : ℕ} (hd : 1 ≤ d) :
    (graph d hd).nE < 1100 * (d + 1) ∧
    ((graph d hd).maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
    ((graph d hd).nV : ℝ) ≤ polyBound 256 d :=
  ⟨graph_edge_bound hd, graph_maxDeg_bound hd, graph_vertex_bound hd⟩

end DetDLP.w4_M5GraphBounds


