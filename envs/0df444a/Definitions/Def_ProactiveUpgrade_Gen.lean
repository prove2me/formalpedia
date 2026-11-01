-- Prove2me | Definitions.Def_ProactiveUpgrade_Gen
-- name    : ProactiveUpgrade_Gen
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:55.50086+00:00
-- url     : https://prove2.me/theorems/17ff0431-3f21-4e37-878d-13a1087014a5
-- title:
--   The generator set $\mathcal F=\{-e_1,d_2,\dots,d_m,e_m\}$
-- statement:
--   The anti-multimodularity of the paper is taken with respect to
--
--   $$
--   \mathcal F=\{-e_1,\ d_2,\ \dots,\ d_m,\ e_m\},\qquad d_i=e_{i-1}-e_i\ (i=2,\dots,m).
--   $$
--
--   Each generator carries its difference operator $\Delta_a$ from the definitions on p.31: $\Delta_{-e_1}$, $\Delta_{d_i}$ (with its shift $-e_{i-1}$) and $\Delta_{e_m}$.
--
--   **Formalization Note** The generators are an inductive type (`negFirst`, `d k`, `posLast`) so that each carries its operator; `gens n` is the set of their vectors. For $n=0$ there is no generator, and for $n=1$, $\mathcal F=\{-e_1,e_1\}$. The paper defines $\mathcal F$ only inside the proof of Lemma A.1 ("Recall that $\mathcal F=\dots$") and $d_i$ only through $\Delta_{d_i}$.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Proof of Lemma A.1, p.31

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir

namespace ProactiveUpgrade

/-- **The generator set `𝓕 = {−e₁, d₂, …, d_m, e_m}`** (Chen et al., SSRN 3777846, Proof of
Lemma A.1, p.31: "Recall that 𝓕 = {−e₁, d₂, ..., d_m, e_m}"), with `dᵢ = e_{i−1} − eᵢ` read off the
definition of `∆_{dᵢ}` (p.31).

`negFirst` is `−e₁`, `d k` is `d_{k+1}` in 1-based numbering (`0 < k.val`), `posLast` is `e_m`.

**Formalization Note** For `n = 0` there is no generator; for `n = 1`, `𝓕 = {−e₁, e₁}`. -/
inductive Gen (n : ℕ) where
  | negFirst (h : 0 < n)
  | d (k : Fin n) (hk : 0 < k.val)
  | posLast (h : 0 < n)

/-- The difference operator `∆_a` of a generator `a ∈ 𝓕` (p.31). -/
def Gen.toDir {n : ℕ} : Gen n → Dir n
  | .negFirst h => Dir.negE ⟨0, h⟩
  | .d k hk => Dir.dd k hk
  | .posLast h => Dir.posE ⟨n - 1, by omega⟩

/-- The vector of a generator: `−e₁`, `d_k = e_{k−1} − e_k`, or `e_m`. -/
def Gen.vec {n : ℕ} (a : Gen n) : Fin n → ℤ :=
  a.toDir.vec

/-- `𝓕` as a set of vectors of `ℤⁿ`. -/
def gens (n : ℕ) : Set (Fin n → ℤ) :=
  Set.range (Gen.vec (n := n))

end ProactiveUpgrade


