-- Prove2me | Definitions.Def_SmallBiasPRF_IsPerfectERF
-- name    : SmallBiasPRF_IsPerfectERF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:40.57102+00:00
-- url     : https://prove2.me/theorems/874ffb1c-bf9e-4f89-bd39-d1ca11813f93
-- title:
--   Perfect $k$-exposure-resilient function (Definition 1)
-- statement:
--   Let $R:\mathbb F_2^{c_1}\to\mathbb F_2^{c_2}$ be a function and let $1\le k\le c_1$. The map $R$ is a **perfect $k$-exposure-resilient function** ($k$-ERF) if, for uniformly distributed $x\in\mathbb F_2^{c_1}$, the output $R(x)$ is uniformly distributed even after conditioning on the values of any $c_1-k$ bits of $x$: for every set $I\subseteq[c_1]$ with $|I|=c_1-k$, every assignment $x'$ of the coordinates in $I$, and every $y\in\mathbb F_2^{c_2}$,
--
--   $$\Pr\big[R(x)=y\ \big|\ x_i=x'_i\ \text{for all } i\in I\big]=2^{-c_2}.$$
--
--   In the construction, a linear perfect $k$-ERF $R:\mathbb F_2^{m_2}\to\mathbb F_2^n$ compresses the $m_2$ output bits of the mod-3 accumulator to $n$ output bits; Lemma 3 characterizes linear perfect ERFs through the minimum distance of the transposed code.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2` and coordinates are 0-based. The conditional probability is written in counting form: the number of $x$ that agree with $x'$ on $I$ and satisfy $R(x)=y$, multiplied by $2^{c_2}$, equals the number of $x$ that agree with $x'$ on $I$ (a nonempty event). The assignment $x'$ is a full vector read only on $I$. The range $1\le k\le c_1$ is part of the definition.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Definition 1, p.12 (PDF 15)

import Mathlib

namespace SmallBiasPRF

/-- **Perfect exposure-resilient function** (Definition 1, p.12 (PDF p.15)).
I. Dinur and Y. Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits
with Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…),
Definition 1, p.12 (PDF p.15).

Let `R : 𝔽₂^{c₁} → 𝔽₂^{c₂}` be a function and `1 ≤ k ≤ c₁`. `R` is a perfect `k`-ERF if, for
uniformly distributed `x ∈ 𝔽₂^{c₁}`, `R(x)` is uniformly distributed conditioned on the values of any
`c₁ − k` bits of `x`: for every set `I ⊆ [c₁]` of `c₁ − k` coordinates, every assignment `x′` of
those coordinates and every `y ∈ 𝔽₂^{c₂}`,
`Pr[R(x) = y | x_i = x′_i for all i ∈ I] = 2^{−c₂}`.

**Formalization Note.** `𝔽₂` is `ZMod 2` and `[c] = Fin c` (0-based). The conditional probability is
written in multiplied counting form: the number of `x` agreeing with `x′` on `I` and mapped to `y`,
times `2^{c₂}`, equals the number of `x` agreeing with `x′` on `I` (that event is never empty). The
paper's `x′ ∈ 𝔽₂^{c₁−k}`, indexed through `I = {i₁, …, i_{c₁−k}}`, is given as a full vector
`x′ : Fin c₁ → ZMod 2` read only on `I`; this changes no instance. The range `1 ≤ k ≤ c₁` is part of
the definition, as in the paper. -/
def IsPerfectERF {c₁ c₂ : ℕ} (R : (Fin c₁ → ZMod 2) → (Fin c₂ → ZMod 2)) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ c₁ ∧
    ∀ I : Finset (Fin c₁), I.card = c₁ - k → ∀ x' : Fin c₁ → ZMod 2, ∀ y : Fin c₂ → ZMod 2,
      (Finset.univ.filter
          (fun x : Fin c₁ → ZMod 2 => (∀ i ∈ I, x i = x' i) ∧ R x = y)).card * 2 ^ c₂ =
        (Finset.univ.filter (fun x : Fin c₁ → ZMod 2 => ∀ i ∈ I, x i = x' i)).card

end SmallBiasPRF


