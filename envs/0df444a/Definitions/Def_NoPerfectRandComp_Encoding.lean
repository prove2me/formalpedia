-- Prove2me | Definitions.Def_NoPerfectRandComp_Encoding
-- name    : NoPerfectRandComp_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:56.069658+00:00
-- url     : https://prove2.me/theorems/c562bbb3-b7ba-48bf-8265-5eb9b0453029
-- title:
--   Private cell encoding of an alphabet $\Gamma$ in $36a$ bits
-- statement:
--   A **private cell encoding** of a finite alphabet $\Gamma$ in $36a$ bits consists of a linear map $H : \mathbb F_2^{36a} \to \mathbb F_2^a$ with private marginals and a total surjective decoder $\mathrm{dec} : \mathbb F_2^a \to \Gamma$. A physical cell $y \in \{0,1\}^{36a}$ decodes to the symbol $\mathrm{dec}(H(y))$.
--
--   Both total functions of the mission are built by decoding their cells this way: the certificate cells of $W_q$ (with $a = a_q$) and the pointer cells of $\hat M_q$ (with $a = b_q$).
--
--   **Formalization Note** The paper fixes one such encoding (the lexicographically first matrix and surjection; for the pointer alphabet an injection into $\{0,1\}^{b_q}$ with a decoder inverting it, which is a surjection with a section). Here the encoding is a parameter of the functions, and every statement about them holds for every admissible encoding; Lemma 4.5 shows that admissible encodings exist.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.5 and its proof, pp.14–15; §4.4, p.16; §5.1, p.19

import Mathlib
import Definitions.Def_NoPerfectRandComp_IsPrivateMap

namespace NoPerfectRandComp

/-- A private cell encoding of the alphabet `Γ` in `36a` bits (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Lemma 4.5, p.14; §4.4,
p.16; §5.1, p.19): a private linear map `H : 𝔽₂^{36a} → 𝔽₂^a` (`IsPrivateMap`) and a total
surjective decoder `dec : 𝔽₂^a → Γ`. A physical cell is decoded as `dec ∘ H`.

**Formalization Note** The paper fixes one such encoding (the lexicographically first matrix and
surjection, p.15; for the pointer alphabet an injection into `{0,1}^{b_q}` with a decoder that
inverts it, p.19, which is a surjection with a section). The functions of this mission take the
encoding as a parameter, and every statement about them is made for every admissible encoding. -/
structure Encoding (a : ℕ) (Γ : Type) where
  /-- the private linear map `H_a` -/
  H : (Fin (36 * a) → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2)
  /-- `H_a` has private marginals -/
  priv : IsPrivateMap a H
  /-- the decoder from payloads to symbols -/
  dec : (Fin a → ZMod 2) → Γ
  /-- the decoder is total and onto the alphabet -/
  surj : Function.Surjective dec

/-- Decode a `36a`-bit Boolean cell: read the bits in `𝔽₂`, apply `H`, then `dec`. -/
def Encoding.decode {a : ℕ} {Γ : Type} (e : Encoding a Γ) (y : Fin (36 * a) → Bool) : Γ :=
  e.dec (e.H (fun j => if y j then 1 else 0))

end NoPerfectRandComp


