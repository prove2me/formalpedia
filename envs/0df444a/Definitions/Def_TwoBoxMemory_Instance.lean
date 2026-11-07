-- Prove2me | Definitions.Def_TwoBoxMemory_Instance
-- name    : TwoBoxMemory_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:46.864088+00:00
-- url     : https://prove2.me/theorems/2fca2bc0-b25e-44d2-a39e-714a55b95bde
-- title:
--   The rational instance: $C^*$, the dyadic cost $C_0$, the 29-cycle and $g^*$
-- statement:
--   The finite instance has failure probabilities $r=1/7$, $s=2/3$ and $D=1$.
--
--   1. $C^*=v/u$ is the saddle cost at the index $\beta=5/4$.
--   2. The explicit dyadic physical cost is
--   $$C_0=\frac{254613987398388214970098320848945712466442749572012796843191368}{2^{200}} .$$
--   3. The **29-cycle** is the word $\mathtt{ABBBBBABBBBBABBBBABBBBBABBBBB}$ (five $A$'s, 24 $B$'s), realized by the deterministic controller with pure initial label $0$ that emits the $k$-th letter at label $k$ and moves to label $k+1 \bmod 29$.
--   4. $g^*=35195023535349249073699/10014242608881728162181268645284$ is the smallest index gap of (B.17).
--
--   These data state the finite jump between 28 and 29 labels.
--
--   **Formalization Note** In the cycle controller $(K_a)_{kj}=1$ iff the $k$-th letter is $a$ and $j=k+1 \bmod 29$, and $0$ otherwise.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §8, (8.1), p.11 (PDF 13); §B.8, (B.16)–(B.17), p.26 (PDF 28); (B.21), p.27 (PDF 29); Appendix G, p.57 (PDF 59)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle

namespace TwoBoxMemory

/-!
# The rational instance: `C*`, the dyadic cost `C₀`, the 29-cycle and the gap `g*`

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§8 and (8.1), p.11 (PDF 13); §B.8, (B.16)–(B.17), p.26 (PDF 28); (B.21), p.27 (PDF 29);
Appendix G, p.57 (PDF 59).

The instance has `r = 1/7`, `s = 2/3`, `D = 1`. `C* = v/u` is the saddle cost at the index
`β = 5/4`; `C₀ = 254613987398388214970098320848945712466442749572012796843191368 / 2^200` is the
explicit dyadic physical cost (8.1)/(B.21) (a 63-digit, 208-bit numerator). The 29-cycle is the
word `ABBBBBABBBBBABBBBABBBBBABBBBB` (five `A`s, 24 `B`s), realized by the deterministic
controller with pure initial label `0` that emits the `k`-th letter at label `k` and moves from
label `k` to `k + 1 mod 29`. `g* = 35195023535349249073699 / 10014242608881728162181268645284`
is the minimal index gap (B.17).

**Formalization Note.** Commands are `Fin 2` with `0 = A`, `1 = B`. In `cycleController`,
`K a k j = 1` iff the `k`-th letter is `a` and `j = k + 1 mod 29` (`finRotate`), else `0`.
-/

noncomputable section

/-- The auxiliary saddle cost `C* = v/u` at `r = 1/7`, `s = 2/3`, `β = 5/4`, `D = 1`. -/
def Cstar : ℝ := saddleCost (1 / 7) (2 / 3) (5 / 4) 1

/-- The explicit dyadic physical cost `C₀` of (8.1)/(B.21). -/
def C0 : ℝ := 254613987398388214970098320848945712466442749572012796843191368 / 2 ^ 200

/-- The minimal index gap `g*` of (B.17). -/
def gstar : ℝ := 35195023535349249073699 / 10014242608881728162181268645284

/-- The letters of the 29-cycle `ABBBBBABBBBBABBBBABBBBBABBBBB` (`0 = A`, `1 = B`). -/
def cycle29 : Fin 29 → Fin 2 :=
  ![0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1]

/-- The deterministic 29-label controller realizing the 29-cycle from the pure initial label
`0`: at label `k` it emits `cycle29 k` and moves to label `k + 1 mod 29`. -/
def cycleController : Controller 29 where
  μ := fun i => if i = 0 then 1 else 0
  K := fun a i j => if j = finRotate 29 i then (if cycle29 i = a then 1 else 0) else 0
  μ_nonneg := fun i => by positivity
  μ_sum := by simp
  K_nonneg := fun a i j => by positivity
  K_row := fun i => by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases Fin.exists_fin_two.mp ⟨cycle29 i, rfl⟩ with h | h <;> simp [h]

end

end TwoBoxMemory


