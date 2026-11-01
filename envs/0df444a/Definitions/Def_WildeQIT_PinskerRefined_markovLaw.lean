-- Prove2me | Definitions.Def_WildeQIT_PinskerRefined_markovLaw
-- name    : WildeQIT_PinskerRefined_markovLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:01.149991+00:00
-- url     : https://prove2.me/theorems/691d2caa-1f70-4de6-8265-841d31eff15f
-- title:
--   The Markov law $p_{X|Z}\,p_{Y|Z}\,p_Z$ of $X - Z - Y$
-- statement:
--   Let $X,Y,Z$ be discrete random variables on finite alphabets $\mathcal X,\mathcal Y,\mathcal Z$ with joint distribution $p_{XYZ}$, marginals $p_{XZ}$, $p_{YZ}$ and $p_Z$. The distribution $p_{X|Z}\,p_{Y|Z}\,p_Z$ "which corresponds to the Markov chain $X - Z - Y$" (Theorem 10.8.3) is
--
--   $$
--   \bigl(p_{X|Z}\,p_{Y|Z}\,p_Z\bigr)(x,y,z)=p_{X|Z}(x|z)\,p_{Y|Z}(y|z)\,p_Z(z)=\frac{p_{XZ}(x,z)\,p_{YZ}(y,z)}{p_Z(z)} ,
--   $$
--
--   and it is $0$ when $p_Z(z)=0$. It is a probability distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$ with the same $XZ$ and $YZ$ marginals as $p_{XYZ}$, under which $X$ and $Y$ are conditionally independent given $Z$. Its trace distance from $p_{XYZ}$ measures how far $p_{XYZ}$ is from being a Markov chain $X - Z - Y$.
--
--   **Formalization Note** The value at $p_Z(z)=0$ is Lean's $a/0=0$; there $p_{XZ}(x,z)=p_{YZ}(y,z)=0$, so $0$ is the only value that keeps the total mass $1$. The definition carries the proof that the masses sum to one, so it is a `WildeQIT.FinDist`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.8.3, p. 314 (the distribution p_{X|Z} p_{Y|Z} p_Z)

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Algebra.BigOperators.Field

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **The Markov law `p_{X|Z} p_{Y|Z} p_Z`**, Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 10.8.3, p. 314: for a joint distribution `p_{XYZ}` on `𝒳 × 𝒴 × 𝒵`,
"another distribution which corresponds to the Markov chain `X − Z − Y`",
`(p_{X|Z} p_{Y|Z} p_Z)(x, y, z) = p_{X|Z}(x|z) p_{Y|Z}(y|z) p_Z(z) = p_{XZ}(x,z) p_{YZ}(y,z) / p_Z(z)`.

**Formalization Note** The triple `(x, y, z)` is `(x, (y, z))`. When `p_Z(z) = 0` the conditional
distributions are undefined; the value is then `0` (Lean's `a / 0 = 0`), which is the only
choice making the law a probability distribution, since `p_{XZ}(x,z) = p_{YZ}(y,z) = 0` there.
Here `p_Z(z) = ∑_y ∑_x p(x,y,z)` is the `Z`-marginal of `p_{YZ}`. -/
noncomputable def markovLaw {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) : FinDist (α × β × γ) where
  prob t := p.margXZ.prob (t.1, t.2.2) * p.margYZ.prob (t.2.1, t.2.2) / p.margYZ.snd.prob t.2.2
  nonneg t := div_nonneg (mul_nonneg (p.margXZ.nonneg _) (p.margYZ.nonneg _)) (p.margYZ.snd.nonneg _)
  sum_eq_one := by
    have hX : ∀ z, ∑ x, p.margXZ.prob (x, z) = p.margYZ.snd.prob z := by
      intro z
      simp only [FinDist.margXZ_prob, FinDist.snd_prob, FinDist.margYZ_prob]
      exact Finset.sum_comm
    have hY : ∀ z, ∑ y, p.margYZ.prob (y, z) = p.margYZ.snd.prob z := fun z => rfl
    have key : ∀ z, ∑ x, ∑ y,
        p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z
          = p.margYZ.snd.prob z := by
      intro z
      have h1 : ∑ x, ∑ y, p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z
          = (∑ x, p.margXZ.prob (x, z)) * (∑ y, p.margYZ.prob (y, z))
              / p.margYZ.snd.prob z := by
        rw [Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_div]
      rw [h1, hX, hY]
      rcases eq_or_ne (p.margYZ.snd.prob z) 0 with h | h
      · rw [h]; simp
      · rw [mul_div_assoc, div_self h, mul_one]
    calc ∑ t : α × β × γ,
          p.margXZ.prob (t.1, t.2.2) * p.margYZ.prob (t.2.1, t.2.2) / p.margYZ.snd.prob t.2.2
        = ∑ x, ∑ y, ∑ z,
            p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type]
      _ = ∑ x, ∑ z, ∑ y,
            p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ z, ∑ x, ∑ y,
            p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z :=
          Finset.sum_comm
      _ = ∑ z, p.margYZ.snd.prob z := Finset.sum_congr rfl fun z _ => key z
      _ = 1 := p.margYZ.snd.sum_eq_one

@[simp] theorem markovLaw_prob {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) (x : α) (y : β) (z : γ) :
    (markovLaw p).prob (x, y, z)
      = p.margXZ.prob (x, z) * p.margYZ.prob (y, z) / p.margYZ.snd.prob z := rfl

end WildeQIT.PinskerRefined


