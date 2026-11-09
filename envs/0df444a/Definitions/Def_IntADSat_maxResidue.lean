-- Prove2me | Definitions.Def_IntADSat_maxResidue
-- name    : IntADSat_maxResidue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:14.833814+00:00
-- url     : https://prove2.me/theorems/c5f1b30f-6d59-42fe-8c3a-d765cf46dbdc
-- title:
--   Largest degree-residue class $m_p(G)$
-- statement:
--   For an integer modulus $p\ge 1$ and a simple graph $G$ on $[n]$,
--
--   $$
--   m_p(G)=\max_{a\in\mathbb Z/p\mathbb Z}\big|\{v:\ \deg_G(v)\equiv a\pmod p\}\big| .
--   $$
--
--   **Formalization Note** Residues are represented by $a\in\{0,\dots,p-1\}$ and the congruence by $\deg_G(v)\bmod p=a$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.3, p.36 (PDF 37)

import Mathlib
import Definitions.Def_IntADSat_deg

set_option autoImplicit false

namespace IntADSat

/-- `m_p(G) = max_{a ∈ ℤ/pℤ} |{v : deg_G(v) ≡ a (mod p)}|` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S3.3, p.36 (PDF 37)),
for an integer modulus `p ≥ 1`.

**Formalization Note** Residues are represented by `a ∈ {0, …, p − 1}` and `deg_G(v) ≡ a` by
`deg_G(v) % p = a`. -/
noncomputable def maxResidue {n : ℕ} (p : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.range p).sup fun a => (Finset.univ.filter fun v => deg G v % p = a).card

end IntADSat


