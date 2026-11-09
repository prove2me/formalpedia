-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Complexity
-- name    : UniversalNonstochastic_Main_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:59:49.800891+00:00
-- url     : https://prove2.me/theorems/bcbf2fa2-fc1c-4085-95d5-e8371d529dfb
-- title:
--   Optimal plain and prefix decoders; complexities $C$, $K$ and their conditional versions
-- statement:
--   Finite objects are coded by natural numbers. A **decoder** is a partial map $D(p,y)$ sending a binary program $p\in\{0,1\}^*$ and an auxiliary input $y$ (a code) to a code. The **description length** of $x$ given $y$ is
--   $$\ell_D(x\mid y)=\min\{|p| : D(p,y)=x\}\in\mathbb N_0\cup\{\infty\},$$
--   equal to $\infty$ only when $x$ has no description given $y$. A decoder is **prefix-free** (self-delimiting) if, for each fixed $y$, no program in its halting domain is a proper prefix of another.
--
--   1. An **optimal plain decoder** $V$ is a partial computable decoder such that for every partial computable decoder $D$ there is a constant $c$ with $\ell_V(x\mid y)\le\ell_D(x\mid y)+c$ for all $x,y$.
--   2. An **optimal prefix decoder** $U$ is a partial computable prefix-free decoder that is optimal, in the same sense, among all partial computable prefix-free decoders.
--
--   Plain and prefix conditional complexities are $C(x\mid y)=\ell_V(x\mid y)$ and $K(x\mid y)=\ell_U(x\mid y)$. The unconditional complexities are $C(x)=C(x\mid 0)$ and $K(x)=K(x\mid 0)$, with $0$ as the empty auxiliary input. Optimality over conditional decoders implies optimality of these among unconditional decoders.
--
--   The codes are as follows. An object $\omega\in\mathbb N$ is coded by itself. A finite set $\Omega\subseteq\mathbb N$ is coded by the standard code of the increasing list of its elements. Hence $K(\Omega)$, $K(\omega\mid\Omega)$, $C(\omega)$ and $C(\omega\mid\Omega)$ are the corresponding complexities of these codes.
--
--   Optimal decoders of both kinds exist (the invariance theorems; see [16, Sects. 1.1 and 4.3], the references the source cites for $C$ and $K$). Every result of the mission holds for every choice of them.
--
--   **Formalization Note** Complexities take values in $\mathbb N_0\cup\{\infty\}$ (`ℕ∞`), the exact infimum. Optimality rules out the value $\infty$, because some partial computable (prefix-free) decoder describes every code. Where complexities are subtracted they are viewed in the extended reals.
--
--   For another computably encoded object space, `KobjOn` is the complexity of its image under the fixed bijection, exactly as on source p.5.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. 1 p.4 and Sect. 1–2 p.5 (C plain complexity, K prefix complexity, optimal decoders, conditional complexities, objects identified with ℕ)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective

open scoped ENNReal

namespace UniversalNonstochastic.Main

/-- A conditional decoder (machine): a partial map sending a binary program `p` and an
auxiliary input `y` (the code of a finite object) to the code of a finite object.
Finite objects are coded by natural numbers. -/
abbrev Decoder := List Bool × ℕ →. ℕ

/-- Description length of `x` given `y` with respect to the decoder `D`: the minimum length
of a program `p` with `D(p, y) = x`, in `ℕ∞`. The value is `⊤` only when `x` has no
description given `y`. -/
noncomputable def descLen (D : Decoder) (x y : ℕ) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : x ∈ D (p, y)), (p.length : ℕ∞)

/-- A decoder is prefix-free (self-delimiting) when, for each fixed auxiliary input `y`,
no program in its halting domain is a proper prefix of another one. -/
def IsPrefixFree (D : Decoder) : Prop :=
  ∀ (y : ℕ) (p q : List Bool), (D (p, y)).Dom → (D (q, y)).Dom → p <+: q → p = q

/-- An optimal plain conditional decoder: a partial computable decoder whose description
lengths are minimal, to within an additive constant, among all partial computable decoders. -/
structure OptimalPlainDecoder where
  dec : Decoder
  partrec : Partrec dec
  optimal : ∀ D : Decoder, Partrec D → ∃ c : ℕ, ∀ x y, descLen dec x y ≤ descLen D x y + c

/-- An optimal prefix conditional decoder: a partial computable prefix-free decoder whose
description lengths are minimal, to within an additive constant, among all partial
computable prefix-free decoders. -/
structure OptimalPrefixDecoder where
  dec : Decoder
  partrec : Partrec dec
  prefixFree : IsPrefixFree dec
  optimal : ∀ D : Decoder, Partrec D → IsPrefixFree D →
    ∃ c : ℕ, ∀ x y, descLen dec x y ≤ descLen D x y + c

/-- Conditional plain complexity `C(x | y)` of codes. -/
noncomputable def OptimalPlainDecoder.C (V : OptimalPlainDecoder) (x y : ℕ) : ℕ∞ :=
  descLen V.dec x y

/-- Conditional prefix complexity `K(x | y)` of codes. -/
noncomputable def OptimalPrefixDecoder.K (U : OptimalPrefixDecoder) (x y : ℕ) : ℕ∞ :=
  descLen U.dec x y

/-- The empty auxiliary input, used for unconditional complexities: `C(x) = C(x | 0)`,
`K(x) = K(x | 0)`. (`0` is also the code of the empty list.) -/
def noCond : ℕ := 0

/-- The code of an object `ω ∈ ℕ = {1, 2, …}`: the number itself. -/
def objCode (ω : ℕ+) : ℕ := (ω : ℕ)

/-- The code of a finite set `Ω ⊆ ℕ`: the standard code of the increasing list of its elements. -/
def setCode (Ω : Finset ℕ+) : ℕ :=
  Encodable.encode ((Ω.sort (· ≤ ·)).map fun a : ℕ+ => (a : ℕ))

/-- Prefix complexity of an object, `K(ω)`. -/
noncomputable def Kobj (U : OptimalPrefixDecoder) (ω : ℕ+) : ℕ∞ := U.K (objCode ω) noCond

/-- Complexity on another object space is the complexity of its image (S, p.5). -/
noncomputable def KobjOn {X : Type*} [Primcodable X] (e : ObjectEncoding X)
    (U : OptimalPrefixDecoder) (ω : X) : ℕ∞ := Kobj U (e.equiv ω)

/-- Plain complexity of an object, `C(ω)`. -/
noncomputable def Cobj (V : OptimalPlainDecoder) (ω : ℕ+) : ℕ∞ := V.C (objCode ω) noCond

/-- Prefix complexity of a finite set, `K(Ω)`. -/
noncomputable def Kset (U : OptimalPrefixDecoder) (Ω : Finset ℕ+) : ℕ∞ := U.K (setCode Ω) noCond

/-- Conditional prefix complexity of an object given a finite set, `K(ω | Ω)`. -/
noncomputable def KobjGivenSet (U : OptimalPrefixDecoder) (ω : ℕ+) (Ω : Finset ℕ+) : ℕ∞ :=
  U.K (objCode ω) (setCode Ω)

/-- Conditional plain complexity of an object given a finite set, `C(ω | Ω)`. -/
noncomputable def CobjGivenSet (V : OptimalPlainDecoder) (ω : ℕ+) (Ω : Finset ℕ+) : ℕ∞ :=
  V.C (objCode ω) (setCode Ω)

/-- A complexity value in `ℕ∞`, viewed in `EReal` (`⊤ ↦ ⊤`). -/
noncomputable def toEReal (n : ℕ∞) : EReal := ((n : ℝ≥0∞) : EReal)

end UniversalNonstochastic.Main


