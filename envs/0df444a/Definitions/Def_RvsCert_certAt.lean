-- Prove2me | Definitions.Def_RvsCert_certAt
-- name    : RvsCert_certAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:35.250199+00:00
-- url     : https://prove2.me/theorems/afb18bdb-a959-4daa-8bd4-43c62af24e2e
-- title:
--   Certificate complexity $C_x(f)$ of an input
-- statement:
--   For a Boolean function $f$ on a finite set $\iota$ of bit positions and an input $x$, $C_x(f)$ is the least size of a certificate for $x$:
--   $$
--   C_x(f)=\min\{|S| : S\subseteq\iota \text{ is a certificate for } x\}.
--   $$
--   The minimum exists because the whole set $\iota$ is always a certificate.
--
--   **Formalization Note** Defined as an infimum of natural numbers; the set is never empty for a finite index set, so the default value of an empty infimum is never used.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 1, p.1 (standard notion, deferred to [BdW02])

import Mathlib
import Definitions.Def_RvsCert_IsCertificate

namespace RvsCert

/-- **Certificate complexity at an input** (standard, [BdW02], as used on p.1–3 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): `certAt f x` is the least size of a certificate for `x`.

**Formalization Note.** Defined as `sInf` in `ℕ`; the set is never empty because
`Finset.univ` is a certificate whenever `ι` is finite (checked in the verification file), so the
junk value `sInf ∅ = 0` never occurs for a `Fintype` index set. -/
noncomputable def certAt {ι : Type} (f : (ι → Bool) → Bool) (x : ι → Bool) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset ι, IsCertificate f x S ∧ S.card = k}

end RvsCert


