-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_BasicKeys
-- name    : ITPIRPreproc_MatchVec_BasicKeys
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:59.893205+00:00
-- url     : https://prove2.me/theorems/9af233a4-c69b-474e-b2af-c85ba0b90720
-- title:
--   §5.2–§5.3 — matrix layout, basic key space $\mathbb F_2^{h\times d}$, selected sets (8) and sampler (9)
-- statement:
--   Let $m=2^h$ and let $u_a,v_a\in\mathbb Z_6^d$ ($a\in[m]$) be matching vectors. The padded database is an $m\times m$ bit matrix; rows are indexed by $a\in[m]$ and columns by $b\in\mathbb F_2^h$, identified with $[m]$ by binary expansion $b\mapsto\sum_t b_t2^t$. A position is a pair $i=(a,b)$.
--
--   The **basic key space** is $\mathcal R=\mathbb F_2^{h\times d}$, and a key $R$ selects one column in every row:
--   $$S(R)=\{(a,Rv_a): a\in[m]\}, \tag{8}$$
--   with the product over $\mathbb F_2$ ($v_a$ reduced mod 2). The compatible keys of $i=(a^\star,b^\star)$ are $\mathcal R_i=\{R: Rv_{a^\star}=b^\star\}$. The **conditional sampler** maps $R_0\in\mathcal R$ to
--   $$R=R_0+(b^\star-R_0v_{a^\star})\,u_{a^\star}^{T}\quad\text{over }\mathbb F_2. \tag{9}$$
--
--   These objects are the subject of Claim 5.2.1, which the analysis of the activation-bit primitive of §6.2 reuses.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §5.2, printed p.16 (PDF p.18); §5.3, printed p.17 (PDF p.19), Eq. (8) and (9)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_MatchingVectors

open scoped ENNReal
open Matrix

namespace ITPIRPreproc.MatchVec

/-!
# The matrix layout and the basic key space (§5.2–§5.3, printed pp.16–17)

"Let m be the least power of two at least max{8, √n}, and set h = log₂ m. Pad the database to
length m² and write it as D ∈ {0,1}^{m×m}. […] Rows are indexed by a ∈ [m], columns by b ∈ F₂^h,
and a target index is denoted i = (a⋆, b⋆)."

"Keys and selected sets. The key space is R = F₂^{h×d}, and for a key R ∈ R the corresponding set
is: S(R) = {(a, Rv_a) : a ∈ [m]}, (8) where the matrix-vector product is over F₂ and b = Rv_a ∈ F₂^h
is identified with an index in [m]."

"To sample from R_i, first sample R₀ ← R and return R = R₀ + (b⋆ − R₀v_{a⋆})u_{a⋆}^T over F₂. (9)"

Here `m = 2^h`; a position is a pair `(a, b) ∈ Fin m × (Fin h → ZMod 2)`; the column `b` is
identified with the index `colIdx b = Σ_t b_t 2^t ∈ [m]` (binary expansion), with inverse
`colVec`. `v₂ a`, `u₂ a` are `v_a, u_a` reduced mod 2 and `v₃ a`, `u₃ a` mod 3.
-/

variable {h d : ℕ}

/-- `v_a mod 2`. -/
def vec2 (x : Fin d → ZMod 6) : Fin d → ZMod 2 :=
  fun k => red2 (x k)

/-- `v_a mod 3`. -/
def vec3 (x : Fin d → ZMod 6) : Fin d → ZMod 3 :=
  fun k => red3 (x k)

/-- The column index in `[m] = Fin (2^h)` of `b ∈ F₂^h`: its binary value `Σ_t b_t 2^t`. -/
def colIdx (b : Fin h → ZMod 2) : Fin (2 ^ h) :=
  ⟨(∑ t : Fin h, (b t).val * 2 ^ t.val) % 2 ^ h, Nat.mod_lt _ (Nat.two_pow_pos h)⟩

/-- The column vector `b ∈ F₂^h` of the index `c ∈ [m]` (its binary digits). -/
def colVec (c : Fin (2 ^ h)) : Fin h → ZMod 2 :=
  fun t => if c.val.testBit t.val then 1 else 0

/-- A position `(a, b) ∈ [m] × F₂^h`. -/
abbrev Pos (h : ℕ) := Fin (2 ^ h) × (Fin h → ZMod 2)

/-- The basic key space `R = F₂^{h×d}`. -/
abbrev BasicKey (h d : ℕ) := Matrix (Fin h) (Fin d) (ZMod 2)

/-- `(a, b) ∈ S(R)` for the basic set (8): `R v_a = b` over `F₂`. -/
def basicSel (v : Fin (2 ^ h) → Fin d → ZMod 6) (R : BasicKey h d) (i : Pos h) : Prop :=
  R *ᵥ vec2 (v i.1) = i.2

instance (v : Fin (2 ^ h) → Fin d → ZMod 6) (R : BasicKey h d) (i : Pos h) :
    Decidable (basicSel v R i) := by
  unfold basicSel; infer_instance

/-- The compatible keys `R_i = {R : i ∈ S(R)}`. -/
def basicCompat (v : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) : Finset (BasicKey h d) :=
  Finset.univ.filter fun R => basicSel v R i

/-- The conditional sampler (9): `R₀ ↦ R₀ + (b⋆ − R₀ v_{a⋆}) u_{a⋆}^T` over `F₂`. -/
def basicSampler (u v : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) (R₀ : BasicKey h d) :
    BasicKey h d :=
  R₀ + Matrix.vecMulVec (i.2 - R₀ *ᵥ vec2 (v i.1)) (vec2 (u i.1))

end ITPIRPreproc.MatchVec


