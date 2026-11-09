-- Prove2me | Definitions.Def_SSNonExt_bitScheme
-- name    : SSNonExt_bitScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:58:25.928056+00:00
-- url     : https://prove2.me/theorems/5fee16da-012e-4cea-aff0-a28d13bfeaea
-- title:
--   The scheme $\Pi_b$ and the class $\mathcal S_b$ on bit strings $\{0,1\}^{b+2}$, with the fourth branch $\bar C_i$
-- statement:
--   To state Theorem 1.1 on bit strings, fix a bijection $\iota:\mathbb F_{2^b}\to\{0,1\}^b$. A **key** in $\{0,1\}^{b+2}$ is two branch bits followed by the $b$ bits $\iota(i)$ of an index $i$; the branch bits $00,01,10$ name $L,R,C$ and $11$ names the **fourth branch** $\bar C_i$ of tagged copies of the central keys. A **share** in $\{0,1\}^{b+1}$ is a tag bit followed by $\iota$ of a value, and a **message** in $\{0,1\}^b$ is read as $\iota^{-1}(m)\in\mathbb F_{2^b}$.
--
--   On $L,R,C$ the bit-string shares are those of table (1); on the fourth branch
--
--   $$\mathrm{Shr}(m,\bar C_i)=\big(\overline{i+m},\ \overline{\alpha\cdot i+m}\big),$$
--
--   both tagged. Reconstruction decodes both shares and applies $\mathrm{Rec}$ (on two tagged shares: remove the tags and apply the central rule), then encodes the result. The source $P_T$ on $\{0,1\}^{b+2}$ is the law of the encoded key when the key is drawn from $U_{\Omega_T}$; it gives probability $0$ to the fourth branch. The class is $\mathcal S_b=\{P_T:T\subseteq V\}$.
--
--   This is the scheme and class of Theorem 1.1: extractors are arbitrary functions on all of $\{0,1\}^{b+2}$, the fourth branch included.
--
--   **Formalization Note** The assignment $L\mapsto00$, $R\mapsto01$, $C\mapsto10$, $\bar C\mapsto11$ is a fixed choice (the paper fixes none); $\iota$ is a parameter. Tag bit `false` means untagged.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), proof of Theorem 1.1, §3.2, p.7 (PDF p.7); Theorem 1.1, p.2

import Mathlib
import Definitions.Def_SSNonExt_sourceClass

namespace SSNonExt

/-- Keys as bit strings `{0,1}^{b+2}` (proof of Theorem 1.1, §3.2, p.7).
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), proof of Theorem 1.1, §3.2, p.7. -/
abbrev BitKey (b : ℕ) : Type := Fin (b + 2) → Bool

/-- Shares as bit strings `{0,1}^{b+1}`: a tag bit followed by `b` bits (§3.2, p.7). -/
abbrev BitShare (b : ℕ) : Type := Fin (b + 1) → Bool

/-- Messages as bit strings `{0,1}^b` ("b-bit messages", Theorem 1.1, p.2). -/
abbrev BitMsg (b : ℕ) : Type := Fin b → Bool

/-- The two branch bits of `L`, `R`, `C`: `L ↦ 00`, `R ↦ 01`, `C ↦ 10`; the fourth pattern `11` is the
branch `C̄` of §3.2.

**Formalization Note.** The paper fixes no assignment of bit patterns to branches; this is one fixed
choice. -/
def branchBits : Branch → Bool × Bool
  | .L => (false, false)
  | .R => (false, true)
  | .C => (true, false)

/-- The encoding of a key `(β, i) ∈ 𝒦` as a bit string: two branch bits (positions `0, 1`) followed by
the `b` bits `ι i` of the index (positions `2, …, b+1`) (§3.2, p.7).

**Formalization Note.** `ι : 𝔽_{2^b} ≃ {0,1}^b` is an arbitrary bijection; every statement quantifies
over it. -/
def encKey {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (k : Key b) : BitKey b :=
  fun p => if h : p.val < 2 then (if p.val = 0 then (branchBits k.1).1 else (branchBits k.1).2)
    else ι k.2 ⟨p.val - 2, by have := p.isLt; omega⟩

/-- The index `i ∈ 𝔽_{2^b}` of a bit-string key: the last `b` bits, read through `ι`. -/
def keyIndex {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (k : BitKey b) : V b :=
  ι.symm fun j => k (j.addNat 2)

/-- The encoding of a share `(τ, x) ∈ {0,1} × V` as a bit string: the tag bit `τ` (`false` =
untagged, `true` = tagged) followed by the `b` bits `ι x` (§3.2, p.7). -/
def encShare {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (s : Share b) : BitShare b :=
  Fin.cons s.1 (ι s.2)

/-- The decoding of a bit-string share: tag bit and value. -/
def decShare {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (s : BitShare b) : Share b :=
  (s 0, ι.symm (Fin.tail s))

/-- The first share of the bit-string scheme (proof of Theorem 1.1, §3.2, p.7). The message `m` is read
as `ι⁻¹ m ∈ 𝔽_{2^b}` and the key as branch bits plus index `i`; on the branches `L, R, C` this is
`F` of table (1), and on the fourth branch `C̄ᵢ` (branch bits `11`) it is the tagged value
`\overline{i + m}`. -/
noncomputable def bitF {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (m : BitMsg b) (k : BitKey b) : BitShare b :=
  encShare ι <|
    match k 0, k 1 with
    | false, false => F (ι.symm m) (Branch.L, keyIndex ι k)
    | false, true => F (ι.symm m) (Branch.R, keyIndex ι k)
    | true, false => F (ι.symm m) (Branch.C, keyIndex ι k)
    | true, true => (true, keyIndex ι k + ι.symm m)

/-- The second share of the bit-string scheme (§3.2, p.7): `G` of table (1) on `L, R, C`, and the
tagged value `\overline{α · i + m}` on the fourth branch `C̄ᵢ`. -/
noncomputable def bitG {b : ℕ} (α : V b) (ι : V b ≃ (Fin b → Bool)) (m : BitMsg b) (k : BitKey b) : BitShare b :=
  encShare ι <|
    match k 0, k 1 with
    | false, false => G α (ι.symm m) (Branch.L, keyIndex ι k)
    | false, true => G α (ι.symm m) (Branch.R, keyIndex ι k)
    | true, false => G α (ι.symm m) (Branch.C, keyIndex ι k)
    | true, true => (true, α * keyIndex ι k + ι.symm m)

/-- The bit-string reconstruction map: decode both shares into tag and value, apply `rec` (which on two
tagged shares removes the tags and applies the central rule, §3.2, p.7), and encode the result. -/
noncomputable def bitRec {b : ℕ} (α : V b) (ι : V b ≃ (Fin b → Bool)) (s₁ s₂ : BitShare b) :
    BitMsg b :=
  ι (rec α (decShare ι s₁) (decShare ι s₂))

/-- The bit-string scheme `Π_b` as a sharing map in the format of Definition 2.1 (party `0` gets the
first share, party `1` the second). -/
noncomputable def bitScheme {b : ℕ} (α : V b) (ι : V b ≃ (Fin b → Bool)) :
    BitMsg b → BitKey b → Fin 2 → BitShare b :=
  fun m k => ![bitF ι m k, bitG α ι m k]

/-- The source `P_T` on `{0,1}^{b+2}`: the law of the encoded key `encKey ι K`, `K ∼ U_{Ω_T}`. It gives
probability zero to the fourth branch. -/
noncomputable def bitP {b : ℕ} (ι : V b ≃ (Fin b → Bool)) (T : Finset (V b)) : PMF (BitKey b) :=
  (srcP T).map (encKey ι)

/-- The source class `𝒮_b = {P_T : T ⊆ V}` on `{0,1}^{b+2}` (Theorem 1.1, p.2; display (2), p.6; §3.2,
p.7). -/
def bitS {b : ℕ} (ι : V b ≃ (Fin b → Bool)) : Set (PMF (BitKey b)) :=
  Set.range (bitP ι)

end SSNonExt


