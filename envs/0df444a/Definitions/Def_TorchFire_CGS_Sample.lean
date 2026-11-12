-- Prove2me | Definitions.Def_TorchFire_CGS_Sample
-- name    : TorchFire_CGS_Sample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:51.793586+00:00
-- url     : https://prove2.me/theorems/b63f7410-fe32-469c-b234-18d87abd5073
-- title:
--   The CGS fire oracles of Construction 4.18: $\mathrm{enc}$, $G$, $\mathrm{Fire.Check}$, $O_b$, $O_2$, $N$, $V$
-- statement:
--   **Construction 4.18** (adapted from [ÇGS26, §6.2]) at security parameter $\mu$: an OSS instance of Construction 4.2 at $\mu$ (19), and independent uniform functions $H_0,H_1:\{0,1\}^{r+\ell}\to\{0,1\}^\mu$, $h:Z\to\{0,1\}^\mu$, with $Z=\{0,1\}^\ell$.
--
--   1. $D_0(y,b,u)=1[u\in W_y]\wedge1[u_1=b]$ (20).
--   2. The query set $Q$ (forward $x$; inverse, dual $(y,u)$; verify $(y,b,u)$) and the injective encoding $\mathrm{enc}:Q\to Z$ that prepends two type bits and pads with zeros (21).
--   3. The common interface $G$: $G(\mathrm{enc}(\mathrm{forward},x))=P(x)$, $G(\mathrm{enc}(\mathrm{inverse},y,u))=P^{-1}(y,u)$, $G(\mathrm{enc}(\mathrm{dual},y,u))=D(y,u)$, $G(\mathrm{enc}(\mathrm{verify},y,b,u))=D_0(y,b,u)$, and $\perp$ outside $\mathrm{enc}(Q)$ (22).
--   4. $\mathrm{Fire.Check}(z,(y,\tau_0,\tau_1))=1[\tau_0=H_0(y\Vert z)]\wedge1[\tau_1=H_1(y\Vert z)]$ (24), zero on malformed (⊥-flagged) tags.
--   5. The public oracles (25): $O_b(y,u,z)=H_b(y\Vert z)$ if $D_0(y,b,u)=1$; $O_2(z,p)=G(z)$ and $N(z,p)=h(z)$ if $\mathrm{Fire.Check}(z,p)=1$; $\perp$ otherwise; $V(z,\eta)=1[\eta=h(z)]$; and the public collection $(D,O_0,O_1,O_2,N,V)$ (26) as one combined oracle. $G,D_0,H_0,H_1,h$ are not public.
--
--   **Formalization Note** The paper allows any polynomially bounded $\ell\ge r+k+3$; the least value $\ell=r+k+3$ is fixed. Tags are passed as held in registers: the two hash values carry the ⊥ flags of the $O_b$ answers they came from.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.18 (19)–(26) pp.26–27; Fact 4.19 p.27

import Mathlib
import Definitions.Def_TorchFire_OSS_signU

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

/-- The length `ℓ = r + k + 3` of the encoded query space `Z = {0,1}^ℓ` (21), p.26.

**Formalization Note** The paper allows any polynomially bounded `ℓ ≥ r + k + 3`; the least value
is fixed here. Nothing in the statements depends on the choice. -/
abbrev ell (mu : ℕ) : ℕ := r mu + k mu + 3

/-- The hash length `µ` of `H_0, H_1, h` (p.27), at the effective parameter `max(µ, 2)`. -/
abbrev hl (mu : ℕ) : ℕ := eff mu

/-- **The oracle distribution of Construction 4.18** (Chatterjee–Mukherjee–Pathak–Podder, *Quantum
Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, pp.26–27, adapted
from [ÇGS26, §6.2]) at security parameter `µ`: an OSS instance of Construction 4.2 at `µ` (19), and
independent uniformly random functions `H_0, H_1 : {0,1}^{r+ℓ} → {0,1}^µ` and
`h : Z → {0,1}^µ`. -/
abbrev Sample (mu : ℕ) : Type :=
  OneSample mu × (Bits (r mu + ell mu) → Bits (hl mu)) × (Bits (r mu + ell mu) → Bits (hl mu)) ×
    (Bits (ell mu) → Bits (hl mu))

noncomputable instance (mu : ℕ) : Fintype (Sample mu) := inferInstance

/-- **The query set** `Q` of the common oracle interface (p.26): forward queries `x ∈ {0,1}^n`,
inverse and dual queries `(y, u)`, verify queries `(y, b, u)`. -/
inductive Query (mu : ℕ) where
  | forward (x : Bits (n mu))
  | inverse (y : Bits (r mu)) (u : Bits (k mu))
  | dual (y : Bits (r mu)) (u : Bits (k mu))
  | verify (y : Bits (r mu)) (b : ZMod 2) (u : Bits (k mu))

variable {mu : ℕ}

/-- **The injective encoding `enc : Q → Z`** (21), p.26: "prepends two type bits to the arguments and
pads with zeros to length `ℓ`" (type bits `00` forward, `01` inverse, `10` dual, `11` verify). -/
def enc : Query mu → Bits (ell mu)
  | .forward x => listToBits _ ([0, 0] ++ bitsToList x)
  | .inverse y u => listToBits _ ([0, 1] ++ bitsToList y ++ bitsToList u)
  | .dual y u => listToBits _ ([1, 0] ++ bitsToList y ++ bitsToList u)
  | .verify y b u => listToBits _ ([1, 1] ++ bitsToList y ++ [b] ++ bitsToList u)

/-- Decoding: the query `q` with `enc(q) = z`, or `⊥` for `z ∉ enc(Q)`. -/
noncomputable def decode (z : Bits (ell mu)) : Option (Query mu) :=
  by classical exact if h : ∃ q, enc q = z then some (Classical.choose h) else none

/-- `D_0(y, b, u) = 1[u ∈ W_y] ∧ 1[u_1 = b]` (20), p.26. -/
noncomputable def D0 (ω : OneSample mu) (y : Bits (r mu)) (b : ZMod 2) (u : Bits (k mu)) : ZMod 2 :=
  by classical exact if InCoset ω y u ∧ firstBit u = b then 1 else 0

/-- The answer register of `G`: one slot for forward answers `P(x) ∈ {0,1}^{r+k}`, one for inverse
answers `π⁻¹(y, w) ∈ {0,1}^n`, one bit for dual and verify answers (zero-padded, paper.md
decision 3). -/
abbrev GAns (mu : ℕ) : Type := (Bits (r mu) × Bits (k mu)) × Bits (n mu) × ZMod 2

instance (mu : ℕ) : Fintype (GAns mu) := inferInstance
instance (mu : ℕ) : DecidableEq (GAns mu) := inferInstance

/-- The value of `G` on a decoded query (22). -/
noncomputable def Gval (ω : OneSample mu) : Query mu → Option (GAns mu)
  | .forward x => some (P ω x, 0, 0)
  | .inverse y u => (Pinv ω (y, u)).map fun x => ((0, 0), x, 0)
  | .dual y u => some ((0, 0), 0, D ω (y, u))
  | .verify y b u => some ((0, 0), 0, D0 ω y b u)

/-- **The common oracle interface `G`** (22), p.26: `G(enc(forward, x)) = P(x)`,
`G(enc(inverse, y, u)) = P⁻¹(y, u)`, `G(enc(dual, y, u)) = D(y, u)`,
`G(enc(verify, y, b, u)) = D_0(y, b, u)`; inputs outside `enc(Q)` return `⊥`. Direct access to `G`
is private (Fact 4.19). -/
noncomputable def G (ω : Sample mu) (z : Bits (ell mu)) : Option (GAns mu) :=
  (decode z).bind (Gval ω.1)

/-- A tag `p = (y, τ_0, τ_1) ∈ {0,1}^r × {0,1}^µ × {0,1}^µ` as held in registers: the hash values
come from oracle answer registers and carry their ⊥ flags (a flagged component is a malformed
tag). -/
abbrev TagIn (mu : ℕ) : Type :=
  Bits (r mu) × (ZMod 2 × Bits (hl mu)) × (ZMod 2 × Bits (hl mu))

instance (mu : ℕ) : Fintype (TagIn mu) := inferInstance
instance (mu : ℕ) : DecidableEq (TagIn mu) := inferInstance

/-- **`Fire.Check(z, (y, τ_0, τ_1)) = 1[τ_0 = H_0(y∥z)] ∧ 1[τ_1 = H_1(y∥z)]`** (24), p.27. -/
def check (ω : Sample mu) (z : Bits (ell mu)) (y : Bits (r mu)) (τ0 τ1 : Bits (hl mu)) : Prop :=
  τ0 = ω.2.1 (bappend y z) ∧ τ1 = ω.2.2.1 (bappend y z)

/-- `Fire.Check` on a tag held in registers: zero on malformed (⊥-flagged) tags (p.27, "The
predicate is zero on malformed queries or tags"). -/
def checkIn (ω : Sample mu) (z : Bits (ell mu)) (p : TagIn mu) : Prop :=
  p.2.1.1 = 0 ∧ p.2.2.1 = 0 ∧ check ω z p.1 p.2.1.2 p.2.2.2

noncomputable instance (ω : Sample mu) (z : Bits (ell mu)) (p : TagIn mu) :
    Decidable (checkIn ω z p) := Classical.dec _

/-- `O_b(y, u, z) = H_b(y∥z)` if `D_0(y, b, u) = 1`, else `⊥` (25), p.27. -/
noncomputable def Ob (ω : Sample mu) (b : ZMod 2) (q : Bits (r mu) × Bits (k mu) × Bits (ell mu)) :
    Option (Bits (hl mu)) :=
  if D0 ω.1 q.1 b q.2.1 = 1 then
    some ((if b = 0 then ω.2.1 else ω.2.2.1) (bappend q.1 q.2.2)) else none

/-- `O_2(z, p) = G(z)` if `Fire.Check(z, p) = 1`, else `⊥` (25), p.27. -/
noncomputable def O2 (ω : Sample mu) (q : Bits (ell mu) × TagIn mu) : Option (GAns mu) :=
  if checkIn ω q.1 q.2 then G ω q.1 else none

/-- `N(z, p) = h(z)` if `Fire.Check(z, p) = 1`, else `⊥` (25), p.27. -/
noncomputable def Nh (ω : Sample mu) (q : Bits (ell mu) × TagIn mu) : Option (Bits (hl mu)) :=
  if checkIn ω q.1 q.2 then some (ω.2.2.2 q.1) else none

/-- `V(z, η) = 1[η = h(z)]` (25), p.27. -/
noncomputable def Vh (ω : Sample mu) (q : Bits (ell mu) × Bits (hl mu)) : ZMod 2 :=
  by classical exact if q.2 = ω.2.2.2 q.1 then 1 else 0

/-- The query domain of the public collection `(D, O_0, O_1, O_2, N, V)` (26). -/
abbrev PubDom (mu : ℕ) : Type :=
  (Bits (r mu) × Bits (k mu)) ⊕ (Bits (r mu) × Bits (k mu) × Bits (ell mu)) ⊕
    (Bits (r mu) × Bits (k mu) × Bits (ell mu)) ⊕ (Bits (ell mu) × TagIn mu) ⊕
    (Bits (ell mu) × TagIn mu) ⊕ (Bits (ell mu) × Bits (hl mu))

/-- Its answer register (⊥ flags as in paper.md decision 3). -/
abbrev PubAns (mu : ℕ) : Type :=
  ZMod 2 × (ZMod 2 × Bits (hl mu)) × (ZMod 2 × Bits (hl mu)) × (ZMod 2 × GAns mu) ×
    (ZMod 2 × Bits (hl mu)) × ZMod 2

instance (mu : ℕ) : Fintype (PubDom mu) := inferInstance
instance (mu : ℕ) : DecidableEq (PubDom mu) := inferInstance
instance (mu : ℕ) : Fintype (PubAns mu) := inferInstance
instance (mu : ℕ) : DecidableEq (PubAns mu) := inferInstance

/-- **The public oracle collection `O = (D, O_0, O_1, O_2, N, V)`** (26), p.27, as one combined
oracle. `G, D_0, H_0, H_1, h` are not directly queryable. -/
noncomputable def pubOracle (ω : Sample mu) : PubDom mu → PubAns mu :=
  combine (D ω.1) <| combine (fun q => encBot (Ob ω 0 q)) <| combine (fun q => encBot (Ob ω 1 q)) <|
    combine (fun q => encBot (O2 ω q)) <| combine (fun q => encBot (Nh ω q)) (Vh ω)

end TorchFire.CGS


