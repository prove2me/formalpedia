-- Prove2me | Definitions.Def_BlockSSM_Supplement_Gpr
-- name    : BlockSSM_Supplement_Gpr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:32.767034+00:00
-- url     : https://prove2.me/theorems/531f7254-790e-4e80-8cf4-5ec533cea446
-- title:
--   The groups $G_{p,r}=\bigl(\bigoplus_{\chi\neq0}A_\chi\bigr)\rtimes C_2^r$
-- statement:
--   Let $Q=C_2^r$, written additively as $\mathbb F_2^r$, and identify its character group $\widehat Q=\mathrm{Hom}(Q,\{\pm1\})$ with $\mathbb F_2^r$ via $\chi(q)=(-1)^{\chi\cdot q}$. For each nonzero $\chi\in\widehat Q$ let $A_\chi=(\mathbb F_p,+)$, on which $q\in Q$ acts by multiplication by $\chi(q)$. Put
--   $$
--   G_{p,r}=\Bigl(\bigoplus_{0\neq\chi\in\widehat Q}A_\chi\Bigr)\rtimes Q .
--   $$
--
--   For primes $p>2^r$ these groups have block-size profiles $D_b(G_{p,r})$ that keep decreasing after feasibility (Theorem 15).
--
--   **Formalization Note** Both factors are written multiplicatively (`Multiplicative`), $A$ is the function space on the nonzero characters, and the semidirect product is Mathlib's `SemidirectProduct`. The definition is stated for all $p,r$; Theorem 15 imposes $p$ prime, $p>2^r$, $r\ge2$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §7, p.7 (PDF p.8)

import Mathlib

namespace BlockSSM.Supplement

/-- The sign character `χ(q) = (−1)^{χ·q} ∈ {±1}` of `Q = C₂^r`, with `Q` written additively as
`F₂^r` and `Q̂ = Hom(Q, {±1})` identified with `F₂^r` through the dot product (Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §7, p.7
(PDF p.8)). -/
def charSign {r : ℕ} (χ q : Fin r → ZMod 2) : ℤˣ :=
  if χ ⬝ᵥ q = 0 then 1 else -1

lemma charSign_zero {r : ℕ} (χ : Fin r → ZMod 2) : charSign χ 0 = 1 := by
  simp [charSign]

lemma charSign_add {r : ℕ} (χ q q' : Fin r → ZMod 2) :
    charSign χ (q + q') = charSign χ q * charSign χ q' := by
  unfold charSign
  rw [dotProduct_add]
  generalize χ ⬝ᵥ q = x
  generalize χ ⬝ᵥ q' = y
  fin_cases x <;> fin_cases y <;> decide

/-- The normal subgroup `A = ⨁_{0 ≠ χ ∈ Q̂} A_χ`, `A_χ = (F_p, +)`, written multiplicatively. -/
abbrev GprKernel (p r : ℕ) : Type := Multiplicative ({χ : Fin r → ZMod 2 // χ ≠ 0} → ZMod p)

/-- The complement `Q = C₂^r`, written multiplicatively (`Q ≅ F₂^r`). -/
abbrev GprTop (r : ℕ) : Type := Multiplicative (Fin r → ZMod 2)

/-- `q ∈ Q` acts on `A` by multiplying the `χ`-coordinate by the sign `χ(q)`. -/
def signAut (p r : ℕ) (q : Fin r → ZMod 2) : MulAut (GprKernel p r) where
  toFun a := Multiplicative.ofAdd fun χ => ((charSign χ.1 q : ℤ) : ZMod p) * a.toAdd χ
  invFun a := Multiplicative.ofAdd fun χ => ((charSign χ.1 q : ℤ) : ZMod p) * a.toAdd χ
  left_inv a := by
    refine Multiplicative.toAdd.injective (funext fun χ => ?_)
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  right_inv a := by
    refine Multiplicative.toAdd.injective (funext fun χ => ?_)
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  map_mul' a a' := by
    refine Multiplicative.toAdd.injective (funext fun χ => ?_)
    simp [mul_add]

/-- The action `Q → Aut(A)` by the sign characters. -/
def signAction (p r : ℕ) : GprTop r →* MulAut (GprKernel p r) where
  toFun q := signAut p r q.toAdd
  map_one' := by
    ext a χ
    simp [signAut, charSign_zero]
  map_mul' q q' := by
    ext a χ
    simp [signAut, charSign_add, mul_assoc]

/-- **The group `G_{p,r}`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §7, p.7 (PDF p.8): "Let Q = C₂^r and identify
Q̂ = Hom(Q, {±1}) with F₂^r. Fix a prime p > 2^r. For each 0 ≠ χ ∈ Q̂, let A_χ = (F_p, +), with Q
acting by the sign character χ, and put G_{p,r} = (⨁_{0≠χ∈Q̂} A_χ) ⋊ Q."

**Formalization Note.** `Q = F₂^r` and `A = (Q̂ ∖ {0} → ZMod p)`, both written multiplicatively;
the sign character is `χ(q) = (−1)^{χ·q}` (`charSign`), and `q` multiplies the `χ`-coordinate by
`χ(q)`. The definition is stated for all `p, r`; the paper (and Theorem 15) takes `p` prime with
`p > 2^r`. -/
abbrev Gpr (p r : ℕ) : Type := GprKernel p r ⋊[signAction p r] GprTop r

end BlockSSM.Supplement


