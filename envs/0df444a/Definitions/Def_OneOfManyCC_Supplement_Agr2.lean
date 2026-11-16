-- Prove2me | Definitions.Def_OneOfManyCC_Supplement_Agr2
-- name    : OneOfManyCC_Supplement_Agr2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:20:38.222198+00:00
-- url     : https://prove2.me/theorems/2dd537d3-d130-4b1d-af71-c115084d2695
-- title:
--   The 1-out-of-2 agreement function $\mathrm{Agr}_2(f)$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1,*\}$ be a partial function. The **agreement function** $\mathrm{Agr}_2(f)$ is the partial function on $2n$ bits, read as a pair $(u,v)$ of $n$-bit strings, defined by
--   $$\mathrm{Agr}_2(f)^{-1}(b)=\mathrm{Inj}_2(f^{-1}(b))\quad(b\in\{0,1\}),$$
--   and $*$ elsewhere. That is, $\mathrm{Agr}_2(f)(u,v)=b$ when $u\ne v$ and $f(u)=f(v)=b$, and $\mathrm{Agr}_2(f)(u,v)=*$ otherwise.
--
--   This is the case $k=2$ of Definition 3.3; Theorem 1.5 compares the formula complexity of $f$ with that of $\mathrm{Agr}_2(f)$. The paper uses $\mathrm{Agr}_2(f)$ under the hypothesis $|f^{-1}(0)|,|f^{-1}(1)|\ge 2$.
--
--   **Formalization Note** The $2n$ input bits are indexed by `Fin n ⊕ Fin n`: `Sum.inl j` is bit $j$ of $u$ and `Sum.inr j` is bit $j$ of $v$. `none` is $*$.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Definition 3.3, p.7 (PDF p.8), with k = 2

import Mathlib

namespace OneOfManyCC.Supplement

/-- **The agreement function** `Agr₂(f)` (Definition 3.3 with `k = 2`).
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Definition 3.3, p.7:
"If |f⁻¹(0)|, |f⁻¹(1)| ≥ k, the agreement function Agrk(f) is the partial function on kn bits defined
by Agrk(f)⁻¹(b) = Injk(f⁻¹(b)) for b ∈ {0, 1}, and ∗ elsewhere."

For `k = 2`: on two strings `(u, v)` the value is `b` if `u ≠ v` and `f(u) = f(v) = b`, and `∗`
otherwise.

**Formalization Note.** A partial function is `(ι → Bool) → Option Bool` (`none` = `∗`). The `2n`
input bits are indexed by `Fin n ⊕ Fin n`: `Sum.inl j` is bit `j` of `u`, `Sum.inr j` bit `j` of
`v`. The hypothesis `|f⁻¹(0)|, |f⁻¹(1)| ≥ 2` is carried by the statements that use `Agr₂(f)`. -/
def Agr2 {n : ℕ} (f : (Fin n → Bool) → Option Bool) : (Fin n ⊕ Fin n → Bool) → Option Bool :=
  fun w =>
    let u : Fin n → Bool := fun j => w (Sum.inl j)
    let v : Fin n → Bool := fun j => w (Sum.inr j)
    if u ≠ v ∧ f u = f v then f u else none

end OneOfManyCC.Supplement


