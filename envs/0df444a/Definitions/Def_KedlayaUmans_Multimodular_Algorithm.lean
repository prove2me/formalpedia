-- Prove2me | Definitions.Def_KedlayaUmans_Multimodular_Algorithm
-- name    : KedlayaUmans_Multimodular_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:31.093449+00:00
-- url     : https://prove2.me/theorems/141e34c3-f870-48cb-88f9-3179d09f4bbb
-- title:
--   Algorithm MULTIMODULAR over $\mathbb Z/r\mathbb Z$ (Section 4.2)
-- statement:
--   Let $r \ge 1$, let $m \ge 1$ and $d \ge 2$ be integers, and let $f \in (\mathbb Z/r\mathbb Z)[X_0,\dots,X_{m-1}]$ be a polynomial of degree at most $d-1$ in each variable. **Algorithm MULTIMODULAR** evaluates $f$ at points $\alpha \in (\mathbb Z/r\mathbb Z)^m$ by recursive multimodular reduction, using $t \ge 1$ rounds. For one point $\alpha$, a round consists of five steps.
--
--   1. Lift $f$ to $\tilde f \in \mathbb Z[X_0,\dots,X_{m-1}]$ by replacing each coefficient with its representative in $\{0,\dots,r-1\}$, and lift $\alpha$ coordinatewise to $\tilde\alpha \in \mathbb Z^m$ in the same way.
--   2. Let $p_1,\dots,p_k$ be the primes less than or equal to
--   $$\ell = 16\log\bigl(d^m (r-1)^{md}\bigr).$$
--   3. For each $p_h$, reduce $\tilde f$ and $\tilde\alpha$ modulo $p_h$, obtaining $f_h \in \mathbb F_{p_h}[X_0,\dots,X_{m-1}]$ and $\alpha_h \in \mathbb F_{p_h}^m$.
--   4. If $t = 1$, compute $f_h(\alpha_h) \in \mathbb F_{p_h}$ directly (this is the value Theorem 4.1's evaluation algorithm outputs). If $t > 1$, compute it by running the algorithm recursively on $(f_h, \alpha_h, p_h, t-1)$, with the same degree parameter $d$.
--   5. Take the unique integer in $\{0,\dots,p_1\cdots p_k - 1\}$ congruent to $f_h(\alpha_h)$ modulo $p_h$ for every $h$ (Chinese remainder theorem), and return its reduction modulo $r$.
--
--   The definition also provides the auxiliary objects: the set of primes $p \le x$ for a real $x$, the bound $d^m(r-1)^{md}$, the threshold $\ell$, and the lifts $\tilde f$, $\tilde\alpha$. It is the main object of Theorem 4.2 and the inner subroutine of the extension-ring algorithm.
--
--   **Formalization Note** $\log$ is the natural logarithm; the paper does not specify a base, and the natural log is the strongest reading of Lemma 2.4. The primes $p \le \ell$ for real $\ell$ are the primes $p \le \lfloor \ell\rfloor$; there are none when $\ell < 2$. The $N$ evaluation points are independent, so the algorithm is defined for a single point. The Chinese-remainder step uses only the residues $f_h(\alpha_h)$, through Mathlib's `ZMod.prodEquivPi`. The value for $t = 0$ (not an input of the algorithm) is $0$. The running time is not formalized.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 12, Section 4.2, Algorithm MULTIMODULAR

import Mathlib

namespace KedlayaUmans.Multimodular

open scoped Function

/-- The primes less than or equal to a real number `x`: the primes `p ≤ ⌊x⌋₊`
(empty when `x < 2`). -/
noncomputable def primesUpTo (x : ℝ) : Finset ℕ := Nat.primesLE ⌊x⌋₊

/-- The bound `d^m (r-1)^{md}` of Step 2 of Algorithm MULTIMODULAR. -/
def magnitudeBound (d m r : ℕ) : ℕ := d ^ m * (r - 1) ^ (m * d)

/-- `ℓ = 16 log(d^m (r-1)^{md})` (natural logarithm), Step 2 of Algorithm MULTIMODULAR. -/
noncomputable def ell (d m r : ℕ) : ℝ := 16 * Real.log (magnitudeBound d m r : ℝ)

/-- Distinct primes are pairwise coprime (used to apply the Chinese remainder theorem). -/
theorem primesUpTo_pairwise_coprime (x : ℝ) :
    Pairwise (Nat.Coprime on fun p : (primesUpTo x) => (p : ℕ)) := by
  intro p q hpq
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primesLE p.2
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primesLE q.2
  exact (Nat.coprime_primes hp hq).2 (fun h => hpq (Subtype.ext h))

/-- Step 1: the lift `f̃ ∈ ℤ[X₀, …, X_{m-1}]` of `f ∈ (ℤ/rℤ)[X₀, …, X_{m-1}]`, replacing each
coefficient by its representative in `{0, …, r-1}`. -/
noncomputable def liftPoly {m r : ℕ} (f : MvPolynomial (Fin m) (ZMod r)) : MvPolynomial (Fin m) ℤ :=
  ∑ s ∈ f.support, MvPolynomial.monomial s (((f.coeff s).val : ℕ) : ℤ)

/-- Step 1: the lift `α̃ ∈ ℤ^m` of a point `α ∈ (ℤ/rℤ)^m`, coordinatewise into `{0, …, r-1}`. -/
def liftPoint {m r : ℕ} (α : Fin m → ZMod r) : Fin m → ℤ :=
  fun i => (((α i).val : ℕ) : ℤ)

/-- **Algorithm MULTIMODULAR** (Kedlaya–Umans, §4.2, p. 12), for one evaluation point `α`
(the `N` points are processed independently).  `multimodular d t r f α` runs `t` rounds of
multimodular reduction; `d` is the per-variable degree parameter (it enters `ℓ`) and is passed
unchanged to the recursive calls.

1. lift `f` and `α` to `f̃ ∈ ℤ[X]`, `α̃ ∈ ℤ^m`;
2. take the primes `p ≤ ℓ = 16 log(d^m (r-1)^{md})`;
3. reduce `f̃`, `α̃` modulo each such `p`, obtaining `f_p`, `α_p`;
4. if `t = 1`, compute `f_p(α_p) ∈ 𝔽_p` directly (the output of Theorem 4.1); otherwise
   compute it by `multimodular d (t-1) p f_p α_p`;
5. combine the residues `f_p(α_p)` by the Chinese remainder theorem into the unique integer in
   `{0, …, ∏ p - 1}` and reduce it modulo `r`.

The value for `t = 0` (not an input of the algorithm) is `0`. -/
noncomputable def multimodular (d : ℕ) {m : ℕ} :
    (t r : ℕ) → MvPolynomial (Fin m) (ZMod r) → (Fin m → ZMod r) → ZMod r
  | 0, _, _, _ => 0
  | t + 1, r, f, α =>
    let fL : MvPolynomial (Fin m) ℤ := liftPoly f
    let αL : Fin m → ℤ := liftPoint α
    let S : Finset ℕ := primesUpTo (ell d m r)
    let residues : (p : S) → ZMod (p : ℕ) := fun p =>
      let fp : MvPolynomial (Fin m) (ZMod (p : ℕ)) := MvPolynomial.map (Int.castRingHom _) fL
      let αp : Fin m → ZMod (p : ℕ) := fun i => ((αL i : ℤ) : ZMod (p : ℕ))
      if t = 0 then MvPolynomial.eval αp fp else multimodular d t (p : ℕ) fp αp
    let crt : ZMod (∏ p : S, (p : ℕ)) :=
      (ZMod.prodEquivPi (fun p : S => (p : ℕ)) (primesUpTo_pairwise_coprime _)).symm residues
    ((crt.val : ℕ) : ZMod r)

end KedlayaUmans.Multimodular


