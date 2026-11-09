-- Prove2me | Definitions.Def_QMAvsQCIP_code
-- name    : QMAvsQCIP_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:50.951975+00:00
-- url     : https://prove2.me/theorems/f6a2f4c8-0d99-4d73-a245-c5556a030f4c
-- title:
--   The multiplicity code $C\subseteq\Sigma^q$
-- statement:
--   The **multiplicity code** $C\subseteq\Sigma^q$, $\Sigma=\mathbb F_q^\lambda$, is the image of the multiplicity-code encoding: the words
--   $$
--   \big(f^{[k]}(\alpha)\big)_{\alpha\in\mathbb F_q,\ k<\lambda}
--   $$
--   of all polynomials $f$ over $\mathbb F_q$ of degree less than $\lambda^3$.
--
--   It is the code $C$ of Lemma 2, Definition 8 and the CHS problem; query pairs of the CHS oracles are $(y,v)\in\{0,1\}^\lambda\times C$.
--
--   **Formalization Note** $q$ is a positive integer so that $\mathbb Z/q$ is finite; Lemma 2 makes it prime. A proved sanity check shows $0\in C$ and that $C$ is closed under addition.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18

import Definitions.Def_QMAvsQCIP_multEnc

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **multiplicity code** `C ⊆ Σ^q` (`Σ = F_q^λ`): the image of the encoding `multEnc`,
i.e. the codewords `(f^{[k]}(α))_{α ∈ F_q, k < λ}` of all polynomials `f` of degree `< λ³`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21): "a univariate multiplicity code C ⊆ Σ^q over Σ = F_q^λ with
multiplicity λ and polynomials of degree less than λ³".

**Formalization Note.** `q` is a positive natural (`ℕ+`) so that `ZMod q` is finite; the code
is a `Finset` of words `ZMod q → Sym λ q`. -/
noncomputable def code (lam : ℕ) (q : ℕ+) : Finset (ZMod q → Sym lam q) :=
  Finset.univ.image (multEnc lam q)

end QMAvsQCIP


