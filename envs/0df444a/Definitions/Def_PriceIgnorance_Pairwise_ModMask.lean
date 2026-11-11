-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_ModMask
-- name    : PriceIgnorance_Pairwise_ModMask
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:20.942362+00:00
-- url     : https://prove2.me/theorems/23befb23-d322-4748-84d0-4e3ea3da10a1
-- title:
--   Uniform law on $\mathbb Z_m$ and the modular masking gadgets of Lemmas 2.6 and C.3
-- statement:
--   These are the random variables of Lemmas 2.6 and C.3, written out on explicit probability spaces.
--
--   1. $\mathrm{Uni}(\mathbb Z_m)$ is the uniform distribution on $\mathbb Z_m$ (counting measure divided by $m$; a probability measure for $m\ge1$).
--   2. **Lemma 2.6 gadget** ($n=k+2$). The sample space is $\mathbb Z_m^k\times\mathbb Z_m$ with law $\mathrm{Uni}(\mathbb Z_m)^{\otimes k}\otimes\mu$, where $\mu$ is a distribution on $\mathbb Z_m$. The variables are
--   $$X_1,\dots,X_{n-2}\ \text{(the first $k$ coordinates)},\qquad X_n\sim\mu\ \text{(the last coordinate)},\qquad X_{n-1}=X_n-\sum_{i=1}^{n-2}X_i \pmod m .$$
--   3. **Lemma C.3 gadget.** The sample space is $\mathbb Z_m\times(\mathbb Z_m\times\mathbb Z_m)^K$ with law $\nu\otimes(\mathrm{Uni}\otimes\mathrm{Uni})^{\otimes K}$. Here $Z\sim\nu$ is the first coordinate, $X^{(i)}_1,X^{(i)}_2$ are the two entries of block $i$, and
--   $$X^{(i)}_3=Z-\big(X^{(i)}_1+X^{(i)}_2\big)\pmod m .$$
--   The whole collection $Z,X^{(1)}_1,X^{(1)}_2,X^{(1)}_3,\dots,X^{(K)}_3$ is indexed by $\{0,\dots,3K\}$: index $0$ is $Z$, and index $1+(3i+a)$ is $X^{(i+1)}_{a+1}$.
--   4. The embedding $\mathbb Z_m\to\mathbb R$, $x\mapsto x.\mathrm{val}\in\{0,\dots,m-1\}$, turns these variables into real random variables, so that $k$-wise independence (Definition 2.1) applies.
--
--   These gadgets are the encodings the price-of-ignorance constructions (Theorems 3.16 and 3.19) use to hide a sample in pairwise-independent noise.
--
--   **Formalization Note** Indices are 0-based in Lean: `maskVars k m i` is the paper's $X_{i+1}$, and `tripleVar m K i a` is $X^{(i+1)}_{a+1}$. The embedding into $\mathbb R$ is injective, so independence of the embedded variables is the same as independence of the $\mathbb Z_m$-valued ones.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Lemma 2.6; p. 30, Lemma C.3

import Mathlib

/-!
# Modular masking gadgets (Lemmas 2.6 and C.3)

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 4 (Lemma 2.6), p. 30 (Lemma C.3).

* `unifZMod m`: the uniform law `Uni(ℤ_m)` (counting measure divided by `m`; a probability
  measure for `m ≥ 1`).
* `zr : ℤ_m → ℝ`, `x ↦ x.val ∈ {0, …, m - 1}`: the injective embedding through which
  `ℤ_m`-valued variables are fed to the real-valued `k`-wise independence predicate.
* Lemma 2.6 gadget, with `n = k + 2` and 0-based indices: on the space
  `(ℤ_m)^k × ℤ_m` with law `Uni(ℤ_m)^{⊗k} ⊗ μ`, the variables are `X_i = ω.1 i` for `i < k`
  (the paper's `X_1, …, X_{n-2}`), `X_k = ω.2 − Σ_{l<k} ω.1 l` (the paper's `X_{n-1}`) and
  `X_{k+1} = ω.2` (the paper's `X_n ∼ μ`).
* Lemma C.3 gadget: on `ℤ_m × (ℤ_m × ℤ_m)^K` with law `ν ⊗ (Uni ⊗ Uni)^{⊗K}`, `Z = ω.1`,
  `X^{(i)}_1 = (ω.2 i).1`, `X^{(i)}_2 = (ω.2 i).2`, `X^{(i)}_3 = Z − (X^{(i)}_1 + X^{(i)}_2)`.
  The whole collection `Z, X^{(1)}_1, X^{(1)}_2, X^{(1)}_3, …` is indexed by `Fin (K * 3 + 1)`:
  index `0` is `Z`, index `1 + finProdFinEquiv (i, a)` is `X^{(i)}_{a+1}`.
-/

namespace PriceIgnorance.Pairwise

open MeasureTheory

/-- The uniform distribution `Uni(ℤ_m)` (for `m ≥ 1`). -/
noncomputable def unifZMod (m : ℕ) : Measure (ZMod m) :=
  (m : ENNReal)⁻¹ • Measure.count

/-- The embedding `ℤ_m → ℝ`, `x ↦ x.val`. -/
def zr {m : ℕ} (x : ZMod m) : ℝ :=
  (x.val : ℝ)

/-- The joint law of the Lemma 2.6 gadget: `X_1, …, X_{n-2}` i.i.d. uniform, independent of
`X_n ∼ μ`. -/
noncomputable def maskLaw (k m : ℕ) (μ : Measure (ZMod m)) :
    Measure ((Fin k → ZMod m) × ZMod m) :=
  (Measure.pi fun _ : Fin k => unifZMod m).prod μ

/-- The `n = k + 2` variables of Lemma 2.6 (0-based): `X_i = ω.1 i` for `i < k`,
`X_k = ω.2 − Σ_l ω.1 l (mod m)`, `X_{k+1} = ω.2`. -/
def maskVars (k m : ℕ) (i : Fin (k + 2)) (ω : (Fin k → ZMod m) × ZMod m) : ZMod m :=
  if h : i.val < k then ω.1 ⟨i.val, h⟩
  else if i.val = k then ω.2 - ∑ l, ω.1 l
  else ω.2

/-- The joint law of the Lemma C.3 gadget: `Z ∼ ν`, independent of the i.i.d. uniform masks
`(X^{(i)}_1, X^{(i)}_2)`, `i < K`. -/
noncomputable def tripleLaw (m K : ℕ) (ν : Measure (ZMod m)) :
    Measure (ZMod m × (Fin K → ZMod m × ZMod m)) :=
  ν.prod (Measure.pi fun _ : Fin K => (unifZMod m).prod (unifZMod m))

/-- `X^{(i)}_{a+1}` of Lemma C.3, for `a = 0, 1, 2`. -/
def tripleVar (m K : ℕ) (i : Fin K) (a : Fin 3) (ω : ZMod m × (Fin K → ZMod m × ZMod m)) :
    ZMod m :=
  if a.val = 0 then (ω.2 i).1
  else if a.val = 1 then (ω.2 i).2
  else ω.1 - ((ω.2 i).1 + (ω.2 i).2)

/-- The whole collection `Z, X^{(1)}_1, X^{(1)}_2, X^{(1)}_3, …, X^{(K)}_3` of Lemma C.3, indexed
by `Fin (K * 3 + 1)`: index `0` is `Z`, index `t + 1` is `X^{(i)}_{a+1}` for
`(i, a) = finProdFinEquiv.symm t`. -/
def tripleFamily (m K : ℕ) (t : Fin (K * 3 + 1)) (ω : ZMod m × (Fin K → ZMod m × ZMod m)) :
    ZMod m :=
  Fin.cases ω.1 (fun s => tripleVar m K (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2 ω) t

end PriceIgnorance.Pairwise


