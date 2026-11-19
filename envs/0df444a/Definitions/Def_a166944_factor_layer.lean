-- Prove2me | Definitions.Def_a166944_factor_layer
-- name    : a166944_factor_layer
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-19T04:53:29.002621+00:00
-- url     : https://prove2.me/theorems/dc22606e-44b7-438d-900a-70aedc7540a7
-- title:
--   OEIS A166944 - factor predicates via the gcd, and the small-to-proper step
-- statement:
--   The terminal argument for the OEIS A166944 recurrence certifies that the two neighbours $C-1$ and $C+1$ of the terminal horizon are prime. The certificate the argument actually produces is the absence of a small divisor, not primality itself.
--
--   Write $\operatorname{NoSmallFactor}(N,\rho)$ for: no integer $f$ with $2\le f\le\rho$ divides $N$; and $\operatorname{NoProperFactor}(N)$ for: no $f$ with $2\le f<N$ divides $N$. The second is the proper-divisor form of primality for $N\ge2$.
--
--   The passage from the first to the second runs through the gcd. Fix $j$ with $0<j<N$ and put $g=\gcd(j,N)$. Then $g$ divides both, and if $g>\rho$ then writing $N=g\cdot q$ we have $q\ge2$ as well, so both factors exceed $\rho$ and
--
--   $$
--   N=g\cdot q\ge(\rho+1)^2,
--   $$
--
--   contradicting the horizon bound $N<(\rho+1)^2$. Hence $g\le\rho$, which $\operatorname{NoSmallFactor}(N,\rho)$ rules out; so $g=1$, and every divisor of $N$ that also divides $j$ must be $1$. Taking $j=f$ for a proper divisor $f$ of $N$ gives the conclusion.
--
--   This is the step that turns the coprimality produced by the quiet tail -- a divisor inside the tail would force a nonunit increment there -- into the absence of a proper divisor, which is what makes the next difference record a twin prime.
--
--   **Formalization Note** The predicates quantify over `Fin` bounds, matching the recurrence-side development, and `Nat.dvd_gcd` supplies the final divisor comparison.
-- source:
--   Derived within this development; the Mathlib-side original is RecordReplay.NoSmallFactor with gcd_eq_one_of_no_small_factor and no_proper_factor_of_no_small_factor. See https://github.com/tara-sooo/A166944-Lean

/-!
# Factor predicates for the A166944 development

The terminal argument certifies that the horizon's neighbours `C - 1` and `C + 1`
have no proper divisor. `NoSmallFactor N root` says no `f` with `2 <= f <= root`
divides `N`; `NoProperFactor N` says no `f` with `2 <= f < N` does.

`NoProperFactor` is the proper-divisor condition for primality, kept separate from
`Nat.Prime` so the replay checker can stay on the recurrence-side imports.

The passage from small to proper goes through the gcd. If `g = gcd j N` exceeded
`root`, then `N = g * q` and both factors would be at least `root + 1`, forcing
`N >= (root+1)^2`, which the horizon bound forbids. So `g <= root`, and
`NoSmallFactor` rules that out.
-/

namespace A166944Research

/-- No divisor of `N` lies in `[2, root]`. -/
def NoSmallFactor (N root : Nat) : Prop :=
  ∀ f : Fin (root + 1), 2 ≤ f.val → ¬ f.val ∣ N

/-- For a number at least two, this is the proper-divisor condition for primality. -/
def NoProperFactor (N : Nat) : Prop :=
  ∀ f : Fin N, 2 ≤ f.val → ¬ f.val ∣ N

/-- **The gcd is one when there is no small factor.** -/
theorem gcd_eq_one_of_no_small_factor {N j root : Nat}
    (hj : 0 < j) (hlt : j < N) (hcheck : NoSmallFactor N root)
    (hroot : N < (root + 1) * (root + 1)) : Nat.gcd j N = 1 := by
  let g := Nat.gcd j N
  have hdivj : g ∣ j := Nat.gcd_dvd_left _ _
  have hdivN : g ∣ N := Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hj
  have hgle := Nat.le_of_dvd hj hdivj
  by_cases h : g = 1
  · exact h
  · have hg2 : 2 ≤ g := by omega
    by_cases hsmall : g ≤ root
    · exact False.elim ((hcheck ⟨g, by omega⟩ hg2) hdivN)
    · obtain ⟨q, hq⟩ := hdivN
      have hq2 : 2 ≤ q := by
        by_cases hq' : 2 ≤ q
        · exact hq'
        · have hm := Nat.mul_le_mul_left g (show q ≤ 1 by omega)
          rw [← hq, Nat.mul_one] at hm
          omega
      by_cases hsmall' : q ≤ root
      · have hdivq : q ∣ N := ⟨g, by simpa [Nat.mul_comm] using hq⟩
        exact False.elim ((hcheck ⟨q, by omega⟩ hq2) hdivq)
      · have hm := Nat.mul_le_mul (show root + 1 ≤ g by omega) (show root + 1 ≤ q by omega)
        omega

/-- **From no small factor to no proper factor.** -/
theorem no_proper_factor_of_no_small_factor {N root : Nat}
    (hcheck : NoSmallFactor N root) (hroot : N < (root + 1) * (root + 1)) :
    NoProperFactor N := by
  intro f hf hdiv
  have h := gcd_eq_one_of_no_small_factor (by omega : 0 < f.val) f.isLt hcheck hroot
  have hdvd := Nat.dvd_gcd (Nat.dvd_refl f.val) hdiv
  rw [h] at hdvd
  have := Nat.eq_one_of_dvd_one hdvd
  omega

end A166944Research


