-- Prove2me | Definitions.Def_FlexRigidity_Supplement_Syndrome
-- name    : FlexRigidity_Supplement_Syndrome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:06:43.104217+00:00
-- url     : https://prove2.me/theorems/acf9f9e3-e2ac-4b95-b0df-ccb6e92dab75
-- title:
--   Syndrome schemes with decoding error $C\cdot 2^{-m^{1/3}}$ (Fact 6.3)
-- statement:
--   Let $0\le\delta_{\mathrm{err}}\le 1$. For a length $m$, let $A$ be uniform on $\{0,1\}^m$ and $B=A\oplus N$ with $N$ made of $m$ independent Bernoulli($\delta_{\mathrm{err}}$) bits independent of $A$. A **syndrome scheme** for length $m$ is a pair $(\mathrm{syn},\mathrm{dec})$ with $\mathrm{syn}:\{0,1\}^m\to\{0,1\}^s$, $\mathrm{dec}:\{0,1\}^s\times\{0,1\}^m\to\{0,1\}^m$; its **decoding failure** is $\Pr[\mathrm{dec}(\mathrm{syn}(A),B)\ne A]$.
--
--   A family of schemes $(\mathrm{syn}_m,\mathrm{dec}_m)_{m\ge0}$ with $s_m=\lfloor 2m\,h_{\mathrm{bin}}(\delta_{\mathrm{err}})\rfloor$ is **as specified in Fact 6.3** with constant $C$ if for every $m$
--   $$\Pr[\mathrm{dec}_m(\mathrm{syn}_m(A),B)\ne A]\le C\cdot 2^{-m^{1/3}}.$$
--
--   This is the error-correction guarantee ([Arı10, Theorem 3]) that Protocols 3 and 5 are parameterised by; the constant $C$ is the one hidden in the $O(2^{-m^{1/3}})$ of Theorem 6.6.
--
--   **Formalization Note** The guarantee is required for the distribution of Protocol 3's honest run ($A$ uniform, independent i.i.d. noise of rate $\sqrt2\delta_{\mathrm{hon}}$, p. 64), which every scheme of Fact 6.3 satisfies. Efficiency is not part of the specification.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), Fact 6.3, pp. 62–63

import Mathlib
import Definitions.Def_FlexRigidity_Supplement_Basics

set_option autoImplicit false

noncomputable section

namespace FlexRigidity.Supplement

/-- **Decoding-failure probability of a syndrome scheme** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Fact 6.3, pp. 62–63): `A` uniform on `{0,1}^m`,
`B = A ⊕ N` with `N` i.i.d. Bernoulli(`δ_err`) independent of `A`; Alice sends the `s`-bit syndrome
`syn(A)` and Bob outputs `Â = dec(syn(A), B)`. This is `Pr[Â ≠ A]`. -/
def schemeFail (δerr : ℝ) {m s : ℕ} (syn : (Fin m → Bool) → Fin s → Bool)
    (dec : (Fin s → Bool) → (Fin m → Bool) → (Fin m → Bool)) : ℝ :=
  ∑ a : Fin m → Bool, ∑ e : Fin m → Bool,
    (1 / 2 ^ m : ℝ) * (∏ j, if e j then δerr else 1 - δerr) *
      (if dec (syn a) (xorS a e) ≠ a then 1 else 0)

/-- **Syndrome as specified in Fact 6.3** (p. 63, [Arı10, Theorem 3]): a family of encoders
`syn_m : {0,1}^m → {0,1}^{s_m}` and decoders `dec_m`, with `s_m = ⌊2 m h_bin(δ_err)⌋`, whose decoding
error is `O(2^{−m^{1/3}})` with the explicit constant `C`: `Pr[Â ≠ A] ≤ C·2^{−m^{1/3}}` for every
`m`.

**Formalization Note** The guarantee is required for the distribution that occurs in Protocol 3's
honest run (`A` uniform, independent i.i.d. noise), which every scheme of Fact 6.3 satisfies;
"efficient" is not part of the specification. -/
def IsSyndromeScheme (δerr : ℝ)
    (syn : (m : ℕ) → (Fin m → Bool) → Fin (synLen δerr m) → Bool)
    (dec : (m : ℕ) → (Fin (synLen δerr m) → Bool) → (Fin m → Bool) → (Fin m → Bool))
    (C : ℝ) : Prop :=
  ∀ m : ℕ, schemeFail δerr (syn m) (dec m) ≤ C * (2 : ℝ) ^ (-((m : ℝ) ^ ((1 : ℝ) / 3)))

end FlexRigidity.Supplement


