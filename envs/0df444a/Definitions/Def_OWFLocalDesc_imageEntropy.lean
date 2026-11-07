-- Prove2me | Definitions.Def_OWFLocalDesc_imageEntropy
-- name    : OWFLocalDesc_imageEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:52.383023+00:00
-- url     : https://prove2.me/theorems/09ba0848-c12e-48d7-b760-63744c056464
-- title:
--   Entropy of $f(U|E)$ for a uniform element of a finite set
-- statement:
--   For a nonempty finite set $E$ and a map $f$, the entropy of $f(e)$ for $e$ uniform on $E$ is
--   $$H\big(f(U|E)\big)=\sum_{v\in f(E)}-p(v)\log_2p(v),\qquad p(v)=\frac{|\{e\in E: f(e)=v\}|}{|E|}.$$
--   The notation $U_r|E_r$ of Theorem 4.2 is a uniform seed conditioned to belong to $E_r$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §4.1, pp.16–17

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Entropy of `f(U|E)`.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §4.1, pp.16–17: the Shannon entropy in
bits of `f(e)` for `e` uniform on a nonempty finite set `E` ("U_r|E_r means a uniform seed
conditioned to belong to E_r"): `∑_v −p(v) log₂ p(v)` with `p(v) = |{e ∈ E : f e = v}| / |E|`. -/
noncomputable def imageEntropy {α β : Type} [DecidableEq β] (E : Finset α) (f : α → β) : ℝ :=
  open Classical in
  ∑ v ∈ E.image f,
    -((((E.filter fun e => f e = v).card : ℝ) / E.card) *
      Real.logb 2 (((E.filter fun e => f e = v).card : ℝ) / E.card))

end OWFLocalDesc


