-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_MatchingVectors
-- name    : ITPIRPreproc_MatchVec_MatchingVectors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:05.823635+00:00
-- url     : https://prove2.me/theorems/1e0a6dae-0896-49de-b46a-730b457bbedf
-- title:
--   §5.2, Eq. (7) — matching vectors modulo 6 with distinct mod-2 reductions
-- statement:
--   A family of **matching vectors** of size $m$ and dimension $d$ is a list of pairs $u_a,v_a\in\mathbb Z_6^d$, $a\in[m]$, such that
--   $$\forall a:\ \langle u_a,v_a\rangle_6=1,\qquad \forall a\ne a':\ \langle u_{a'},v_a\rangle_2=0\ \text{ or }\ \langle u_{a'},v_a\rangle_3=0, \tag{7}$$
--   where the subscript denotes reduction of the inner product modulo $6$, $2$, $3$, and such that the vectors $v_a \bmod 2\in\mathbb F_2^d$ are pairwise distinct.
--
--   A family indexed by $h$ (with $m=2^h$ rows and dimension $\dim(h)$) is **computable with constants $C_0,c_0$** by two deterministic word-RAM programs when, for every $h\ge3$: on input $(h,a)$ the first outputs the codes of $u_a,v_a$ ($3$ bits per coordinate) within work $C_0\,d\,h^{c_0}$; on input $h$ the second outputs the codes of all pairs in row order within work $C_0\,m\,d\,h^{c_0}$ and storage $C_0\,m\,d$.
--
--   These are the objects of the matching-vector PIR primitives of §5.3 and §6.2: the diagonal condition makes the target row survive the decoding sum, and the off-diagonal condition cancels every other row either in the column shift (mod 2) or in the weighted sum (mod 3).
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §5.2, printed p.17 (PDF p.19), Eq. (7); Appendix A, printed pp.35–37 (PDF pp.37–39)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Machine

namespace ITPIRPreproc.MatchVec

open WordRAM

/-!
# Matching vectors modulo 6 (§5.2, Eq. (7), printed p.17; Appendix A, pp.35–37)

"There are m pairs u_a, v_a ∈ Z_6^d with d = 2^{O(√(h log h))} such that
∀a : ⟨u_a, v_a⟩_6 = 1, ∀a ≠ a′ : ⟨u_a′, v_a⟩_2 = 0 or ⟨u_a′, v_a⟩_3 = 0. (7)
Here the subscript denotes reduction modulo that integer. […] We also require the vectors
v_a mod 2 to be distinct; each is nonzero by the diagonal condition. Section A discusses how to
adapt prior works to get a construction of such a family in md poly(h) time and O(md) space,
with each vector computable from its row index in d poly(h) time."

Rows are `a ∈ Fin m`; vectors are `Fin d → ZMod 6`; `⟨x, y⟩_6` is `x ⬝ᵥ y` in `ZMod 6`, and
`⟨x, y⟩_2`, `⟨x, y⟩_3` are its images under the ring maps `ZMod 6 → ZMod 2`, `ZMod 6 → ZMod 3`
(which equal the inner products of the reduced vectors).

A vector `x ∈ Z_6^d` is encoded in `3d` bits (`3` bits per coordinate, value `0, …, 5`). A family
indexed by `h` (`m = 2^h` rows of dimension `dim h`) is *computable* with constants `C₀`, `c₀`
by word-RAM programs `vecProg`, `tableProg` when, for every `h ≥ 3`: on input `(h, a)` the
deterministic `vecProg` outputs the codes of `u_a, v_a` within `C₀ · d · h^{c₀}` work; on input
`h` the deterministic `tableProg` outputs the codes of all pairs, in row order, within
`C₀ · m · d · h^{c₀}` work and `C₀ · m · d` working bits.
-/

/-- Reduction `ZMod 6 → ZMod 2`. -/
def red2 : ZMod 6 →+* ZMod 2 :=
  ZMod.castHom (by norm_num) (ZMod 2)

/-- Reduction `ZMod 6 → ZMod 3`. -/
def red3 : ZMod 6 →+* ZMod 3 :=
  ZMod.castHom (by norm_num) (ZMod 3)

/-- A family of `m` pairs `u_a, v_a ∈ Z_6^d` satisfying (7), with the vectors `v_a mod 2`
pairwise distinct. -/
structure IsMVFamily (m d : ℕ) (u v : Fin m → Fin d → ZMod 6) : Prop where
  /-- `⟨u_a, v_a⟩_6 = 1`. -/
  diag : ∀ a, u a ⬝ᵥ v a = 1
  /-- `⟨u_{a′}, v_a⟩_2 = 0` or `⟨u_{a′}, v_a⟩_3 = 0` for `a ≠ a′`. -/
  offdiag : ∀ a a', a ≠ a' → red2 (u a' ⬝ᵥ v a) = 0 ∨ red3 (u a' ⬝ᵥ v a) = 0
  /-- The vectors `v_a mod 2` are pairwise distinct. -/
  distinct_mod2 : Function.Injective fun a => fun k => red2 (v a k)

/-- The `3d`-bit code of a vector of `Z_6^d`. -/
def encZ6Vec {d : ℕ} (x : Fin d → ZMod 6) : List Bool :=
  (List.ofFn fun k => natBits 3 (x k).val).flatten

/-- The code of the whole table `(u_a, v_a)_{a ∈ [m]}` in row order. -/
def mvTableCode {m d : ℕ} (u v : Fin m → Fin d → ZMod 6) : List Bool :=
  (List.ofFn fun a => encZ6Vec (u a) ++ encZ6Vec (v a)).flatten

/-- The family `h ↦ (u h, v h)` (`2^h` rows, dimension `dim h`) is computed, for every `h ≥ 3`,
by the deterministic programs `vecProg` (one pair from its row index, `C₀ d h^{c₀}` work) and
`tableProg` (the whole table, `C₀ m d h^{c₀}` work and `C₀ m d` working bits). -/
def MVComputable (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
    (C₀ : ℝ) (c₀ : ℕ) (vecProg tableProg : Program) : Prop :=
  Deterministic vecProg ∧ Deterministic tableProg ∧
  ∀ h : ℕ, 3 ≤ h →
    (∀ a : Fin (2 ^ h),
      Halts vecProg (encNat h ++ encNat a.val) zeroTape ∧
      output vecProg (encNat h ++ encNat a.val) zeroTape =
        encZ6Vec (u h a) ++ encZ6Vec (v h a) ∧
      (cost vecProg (encNat h ++ encNat a.val) zeroTape : ℝ) ≤ C₀ * dim h * (h : ℝ) ^ c₀) ∧
    (Halts tableProg (encNat h) zeroTape ∧
      output tableProg (encNat h) zeroTape = mvTableCode (u h) (v h) ∧
      (cost tableProg (encNat h) zeroTape : ℝ) ≤ C₀ * 2 ^ h * dim h * (h : ℝ) ^ c₀ ∧
      (workingBits tableProg (encNat h) zeroTape : ℝ) ≤ C₀ * 2 ^ h * dim h)

end ITPIRPreproc.MatchVec


