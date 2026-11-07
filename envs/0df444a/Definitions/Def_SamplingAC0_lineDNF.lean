-- Prove2me | Definitions.Def_SamplingAC0_lineDNF
-- name    : SamplingAC0_lineDNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:32.70831+00:00
-- url     : https://prove2.me/theorems/c4886c5c-6d78-4eb4-b7eb-efa6f72ed313
-- title:
--   Lines of $\mathbb F_q^2$ and the line DNFs $C_\ell$
-- statement:
--   Let $q=2^k$ with $k\ge1$ and $\mathbb F_q$ the field with $q$ elements. Field elements are recorded as $k$-bit strings by a fixed bijection $\mathrm{enc}:\mathbb F_q\to\{0,1\}^k$. The **nonvertical lines** of $\mathbb F_q^2$ are
--
--   $$\ell_{a,t}=\{(x,ax+t)\mid x\in\mathbb F_q\},\qquad a,t\in\mathbb F_q,$$
--
--   $q^2$ of them. The input of the sampler of $R$ consists of $m=2qk$ bits: for each list position $i\in[q]$, the $k$ bits of each coordinate of a point $V_i$. Its outputs are one **line bit** per line and the $m$ point-list bits, $b=q^2+m$ in total.
--
--   The **line DNF** $C_\ell$ for $\ell=\ell_{a,t}$ is the OR, over the list positions $i\in[q]$ and the $q$ points $(x,ax+t)$ of $\ell$, of the term with $2k$ literals saying that the bits of point $i$ equal the encoding of $(x,ax+t)$. It has $q^2$ terms and is true exactly when some listed point lies on $\ell$. The **block sampler** outputs $C_\ell$ on the line positions and the input bit itself (a one-literal DNF) on each point-list position.
--
--   **Formalization Note** $\mathbb F_q$ is `GaloisField 2 k`; the encoding is a parameter `enc` of every definition and every theorem quantifies over it. The terms of $C_\ell$ are listed in a fixed order of the field elements, which affects neither the value nor the size.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8

import Mathlib
import Definitions.Def_SamplingAC0_DNF
set_option autoImplicit false

namespace SamplingAC0

/-- The field `F_q` with `q = 2^k` elements. -/
abbrev F (k : ℕ) : Type := GaloisField 2 k

noncomputable instance instFintypeF (k : ℕ) : Fintype (F k) := Fintype.ofFinite _

noncomputable instance instDecidableEqF (k : ℕ) : DecidableEq (F k) := Classical.decEq _

/-- An encoding of field elements by bit strings, for every `k ≥ 1`: a bijection
`F_{2^k} ≃ {0,1}^k`. The paper "record[s] each point using 2k bits" without naming the encoding.

**Formalization Note.** The bijection is required only for `k ≥ 1` (`q = 2^k ≥ 2`, the paper's
setting). Mathlib's `GaloisField 2 0` is `ZMod 2`, with two elements, so no bijection with
`{0,1}^0` exists there; requiring one for every `k` would make the type of encodings empty. -/
abbrev Encoding : Type := (k : ℕ) → 0 < k → (F k ≃ (Fin k → Bool))

/-- The `k` bits recording a field element (for `k = 0`, the empty string). -/
def Encoding.bits (enc : Encoding) {k : ℕ} (x : F k) : Fin k → Bool :=
  if h : 0 < k then enc k h x else fun _ => false

/-- The field element recorded by `k` bits (the inverse of `Encoding.bits` for `k ≥ 1`; for
`k = 0`, the element `0`). -/
noncomputable def Encoding.read (enc : Encoding) {k : ℕ} (w : Fin k → Bool) : F k :=
  if h : 0 < k then (enc k h).symm w else 0

/-- A nonvertical line `ℓ_{a,t}` of `F_q²`, given by its slope `a` and intercept `t`. -/
abbrev Line (k : ℕ) : Type := F k × F k

/-- The point `v = (x, y)` lies on the line `ℓ_{a,t} = {(x, ax + t) | x ∈ F_q}`. -/
def onLine {k : ℕ} (ℓ : Line k) (v : F k × F k) : Prop := v.2 = ℓ.1 * v.1 + ℓ.2

noncomputable instance {k : ℕ} (ℓ : Line k) (v : F k × F k) : Decidable (onLine ℓ v) := by
  unfold onLine; infer_instance

/-- Input bits of the sampler of `R`: bit `j` of coordinate `c` (`false` = x, `true` = y) of the
listed point `i ∈ [q]`; there are `m = 2qk` of them. -/
abbrev RIn (k : ℕ) : Type := Fin (2 ^ k) × Bool × Fin k

/-- Output positions of `R`: one line bit `C_ℓ` per line, then the `2qk` point-list bits;
there are `b = q² + 2qk` of them. -/
abbrev ROut (k : ℕ) : Type := Line k ⊕ RIn k

/-- The `i`-th listed point, decoded from its `2k` input bits. -/
noncomputable def decodePt (enc : Encoding) {k : ℕ} (x : RIn k → Bool) (i : Fin (2 ^ k)) :
    F k × F k :=
  (enc.read (fun j => x (i, false, j)), enc.read (fun j => x (i, true, j)))

/-- The term with `2k` literals "the bits of point `i` equal the encoding of `v`". -/
def pointTerm (enc : Encoding) {k : ℕ} (i : Fin (2 ^ k)) (v : F k × F k) : Term (RIn k) :=
  (List.finRange k).map (fun j => ((i, false, j), enc.bits v.1 j)) ++
    (List.finRange k).map (fun j => ((i, true, j), enc.bits v.2 j))

/-- **The line DNF `C_ℓ`.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027
submission (manuscript sha256 99c33d30…), §3, p.8: "To compute C_ℓ, take an OR over the q list
positions and the q locations on ℓ, testing equality of their 2k bits. This is an explicit DNF with
q² terms. The point-coordinate outputs are input bits."

`lineDNF enc ℓ` has one term per list position `i` and per point `(x, ax + t)` of `ℓ = ℓ_{a,t}`.
`blockSampler enc k` is the sampler of `R`: `C_ℓ` on the line positions, and the one-literal DNF
`x_p` on the point-list position `p`.

**Formalization Note.** The field elements are enumerated in a fixed order (`Finset.toList`); the
order of the terms does not affect the formula's value or size. -/
noncomputable def lineDNF (enc : Encoding) {k : ℕ} (ℓ : Line k) : DNF (RIn k) :=
  (List.finRange (2 ^ k)).flatMap (fun i =>
    (Finset.univ : Finset (F k)).toList.map (fun x => pointTerm enc i (x, ℓ.1 * x + ℓ.2)))

/-- The DNF sampler of `R` (one DNF per output position). -/
noncomputable def blockSampler (enc : Encoding) (k : ℕ) : ROut k → DNF (RIn k)
  | Sum.inl ℓ => lineDNF enc ℓ
  | Sum.inr p => [[(p, true)]]

end SamplingAC0


