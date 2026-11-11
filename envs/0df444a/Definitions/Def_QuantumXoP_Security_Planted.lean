-- Prove2me | Definitions.Def_QuantumXoP_Security_Planted
-- name    : QuantumXoP_Security_Planted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:32.002193+00:00
-- url     : https://prove2.me/theorems/97df1373-55c4-4538-9a34-43f346e31764
-- title:
--   Planted-collision, planted 4-XOR and small-range distributions; the search distributions $Z_M$, $S_M$
-- statement:
--   All distributions are defined by their sampling procedures. Sampling without replacement $(x_1,\dots,x_m)\leftarrow(\{0,1\}^n)^{(*m)}$ draws pairwise distinct inputs uniformly.
--
--   1. $D_{PC}$: sample $x_1\ne x_2$, then $f\leftarrow F$ uniformly with $f(x_1)=f(x_2)$ (needs $N\ge2$).
--   2. $D_{3PC}$: sample distinct $x_1,x_2,x_3$, then $f$ uniformly with $f(x_1)=f(x_2)=f(x_3)$ (needs $N\ge3$).
--   3. $D_{PC,k}$: sample distinct $(x_1,\dots,x_{2k})$, then $f$ uniformly with $f(x_{2j-1})=f(x_{2j})$ for all $j\in[k]$ (needs $N\ge2k$).
--   4. $D_{4X}$: sample distinct $x_1,\dots,x_4$, then $f$ uniformly with $f(x_1)+f(x_2)+f(x_3)+f(x_4)=0^n$ (needs $N\ge4$).
--   5. **Small range** $S_R$ (Definition 6.3, $R\ge1$): a uniform $f:\{0,1\}^n\to[R]$, an independent uniform $g:[R]\to\{0,1\}^n$, output $h=g\circ f$. The collision count is $C_f=|\{\{x,x'\}:x\ne x',\ f(x)=f(x')\}|$.
--   6. **Search** (Claim B.1): $Z_M$ always outputs the zero function on $[M]$; $S_M$ samples $z\leftarrow[M]$ and outputs $b_z(j)=[\![j=z]\!]$.
--
--   These distributions are the intermediate objects through which §6 and Appendix B bound the degree-2, 3, 4 and 6 components of $\mu_{XoP[r]}$.
--
--   **Formalization Note** The nondegeneracy $N\ge m$ is an argument of each planted law; $[R]$ and $[M]$ are `Fin R`, `Fin M`. Sampling $g$ on all of $[R]$ rather than on the image of $f$ gives the same law of $h$.
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), §6.1 pp. 26–27 (PDF pp. 28–29), Definition 6.3, Lemma 6.5; §6.3–6.4 pp. 28–29 (PDF pp. 30–31); App. B.2 p. 43 (PDF p. 45), Claim B.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

noncomputable section

namespace QuantumXoP.Security

open QAlgorithms

/-!
# Planted and small-range distributions (Choi–Hhan–Jang, §6.1–6.4 pp. 26–30; App. B.2 p. 43)

Every distribution is defined by the sampling procedure printed in the paper, as a `PMF`:
first a uniformly random tuple of *distinct* inputs (`Fin m ↪ Qubits n`, sampling without
replacement, p. 8), then a uniformly random `f ∈ F_n` satisfying the planted constraint.
The constraint set always contains the zero function, so the second step is well defined; the
first step needs `m ≤ 2^n` distinct inputs, which is the hypothesis `hm`.
-/

/-- Sampling without replacement (p. 8): `m` pairwise distinct inputs exist when `m ≤ 2^n`. -/
theorem nonempty_embedding_of_le {n m : ℕ} (hm : m ≤ 2 ^ n) : Nonempty (Fin m ↪ Qubits n) :=
  Function.Embedding.nonempty_of_card_le (by simpa using hm)

open Classical in
/-- The generic planted law: sample distinct `(x_1, …, x_m) ← ({0,1}^n)^{(∗m)}` uniformly, then
`f ← F_n` uniformly among the functions satisfying `Cons x f`. -/
def plantedLaw (n m : ℕ) (hm : m ≤ 2 ^ n) (Cons : (Fin m → Qubits n) → Fn n → Prop)
    (h0 : ∀ x, Cons x 0) : PMF (Fn n) :=
  haveI := nonempty_embedding_of_le hm
  (PMF.uniformOfFintype (Fin m ↪ Qubits n)).bind fun x =>
    PMF.uniformOfFinset (Finset.univ.filter fun f => Cons x f) ⟨0, by simp [h0]⟩

/-- p. 26: `D_PC`, a random function with a planted collision: sample `x_1 ≠ x_2`, then a uniformly
random `f ← F` with `f(x_1) = f(x_2)`. Requires `N = 2^n ≥ 2`. -/
def pcLaw (n : ℕ) (hN : 2 ≤ 2 ^ n) : PMF (Fn n) :=
  plantedLaw n 2 hN (fun x f => f (x 0) = f (x 1)) (fun _ => rfl)

/-- p. 28: `D_3PC`, a random function with a planted 3-collision: sample three distinct
`x_1, x_2, x_3`, then a uniformly random `f ← F` with `f(x_1) = f(x_2) = f(x_3)`. Requires `N ≥ 3`. -/
def pc3Law (n : ℕ) (hN : 3 ≤ 2 ^ n) : PMF (Fn n) :=
  plantedLaw n 3 hN (fun x f => f (x 0) = f (x 1) ∧ f (x 1) = f (x 2)) (fun _ => ⟨rfl, rfl⟩)

/-- p. 29: `D_{PC,k}`, `k` planted collisions: sample distinct `(x_1, …, x_{2k})`, then a uniformly
random `f ← F` with `f(x_{2j−1}) = f(x_{2j})` for all `j ∈ [k]` (0-based: `f(x_{2j}) = f(x_{2j+1})`
for `j < k`). Requires `N ≥ 2k`. `D_{PC,1} = D_PC` and `D_{PC,0} = D_F` (p. 30). -/
def pcKLaw (n k : ℕ) (hN : 2 * k ≤ 2 ^ n) : PMF (Fn n) :=
  plantedLaw n (2 * k) hN
    (fun x f => ∀ j : Fin k,
      f (x ⟨2 * j, by have := j.isLt; omega⟩) = f (x ⟨2 * j + 1, by have := j.isLt; omega⟩))
    (fun _ _ => rfl)

/-- p. 29: `D_4X`, a planted 4-XOR: sample four distinct `x_1, …, x_4`, then a uniformly random
`f ← F` with `f(x_1) + f(x_2) + f(x_3) + f(x_4) = 0^n`. Requires `N ≥ 4`. -/
def x4Law (n : ℕ) (hN : 4 ≤ 2 ^ n) : PMF (Fn n) :=
  plantedLaw n 4 hN (fun x f => f (x 0) + f (x 1) + f (x 2) + f (x 3) = 0) (fun _ => by simp)

/-- Definition 6.3 (p. 26), steps 1–2: the joint law of the uniformly random `f : {0,1}^n → [R]`
and an independent uniformly random `g : [R] → {0,1}^n` (`[R]` is `Fin R`). Sampling `g` on all
of `[R]` instead of only on the image `I` of `f` gives the same law of `h = g ∘ f`. -/
def srJoint (n R : ℕ) [NeZero R] : PMF ((Qubits n → Fin R) × (Fin R → Qubits n)) :=
  PMF.uniformOfFintype _

/-- Definition 6.3 (p. 26): the small-range distribution `S_R` over `F_n`, the law of `h = g ∘ f`. -/
def smallRange (n R : ℕ) [NeZero R] : PMF (Fn n) :=
  (srJoint n R).map fun p => p.2 ∘ p.1

/-- Lemma 6.5 (p. 27): `C_f = |{{x, x′} : x ≠ x′, f(x) = f(x′)}|`, the number of colliding
unordered pairs of `f`. -/
def collCount {n R : ℕ} (f : Qubits n → Fin R) : ℕ :=
  (((Finset.univ : Finset (Qubits n)).powersetCard 2).filter
    fun s => ∀ x ∈ s, ∀ y ∈ s, f x = f y).card

open Classical in
/-- The probability `Pr_{a←μ}[E(a)]` of an event under a law on a finite type. -/
def probOf {α : Type*} [Fintype α] (μ : PMF α) (E : α → Prop) : ℝ :=
  ∑ a, if E a then (μ a).toReal else 0

/-- Claim B.1 (p. 43): `Z_M`, the distribution that always outputs the all-zero function
`b_∅ : [M] → {0,1}`. -/
def zeroLaw (M : ℕ) : PMF (Fin M → Bool) :=
  PMF.pure fun _ => false

/-- Claim B.1 (p. 43): `S_M`, sample `z ← [M]` uniformly and output the indicator
`b_z(j) = ⟦j = z⟧`. Requires `M ≥ 1`. -/
def indicatorLaw (M : ℕ) [NeZero M] : PMF (Fin M → Bool) :=
  (PMF.uniformOfFintype (Fin M)).map fun z j => decide (j = z)

/-! ### Sanity checks -/

example (n : ℕ) (x : Fin 2 → Qubits n) (f : Fn n) :
    (∀ j : Fin 1, f (x ⟨2 * j, by have := j.isLt; omega⟩) = f (x ⟨2 * j + 1, by have := j.isLt; omega⟩))
      ↔ f (x 0) = f (x 1) := by
  constructor
  · intro h; simpa using h 0
  · intro h j; fin_cases j; simpa using h

example {n : ℕ} : collCount (fun _ : Qubits n => (0 : Fin 1)) = ((2 ^ n).choose 2) := by
  simp [collCount, Finset.card_powersetCard]

end QuantumXoP.Security


