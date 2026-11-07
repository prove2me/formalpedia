-- Prove2me | Definitions.Def_OWFLocalDesc_queryMatrix
-- name    : OWFLocalDesc_queryMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:37.391319+00:00
-- url     : https://prove2.me/theorems/0282f6ae-8e16-4fd2-bc86-2ad099b4c6fc
-- title:
--   The query matrix $M_X$ (Lemma 4.4)
-- statement:
--   For $S:\{0,1\}^n\to\mathbb F_2^L$ and points $X=(X_1,\dots,X_m)$, $M_X$ is the $m\times L$ matrix over $\mathbb F_2$ whose $i$-th row is $S(X_i)$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 4.4, p.18

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **The query matrix `M_X` (Lemma 4.4).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 4.4, p.18:
"Let M_X be the matrix whose ith row is S(X_i)." -/
def queryMatrix {m n L : ℕ} (S : (Fin n → Bool) → (Fin L → ZMod 2)) (X : Fin m → Fin n → Bool) :
    Matrix (Fin m) (Fin L) (ZMod 2) :=
  Matrix.of fun i j => S (X i) j

end OWFLocalDesc


