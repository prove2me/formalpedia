-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
-- name    : UniversalNonstochastic_Main_Supplement_Complexities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:24:03.157484+00:00
-- url     : https://prove2.me/theorems/06a2efea-5ba5-42c7-b396-efe99e284b0a
-- title:
--   Complexities of numbers, plain complexities of models, busy beaver $BB$, $BB_C$, inverse busy beaver $\mu$ and $\sigma$
-- statement:
--   Let $U$ be an optimal prefix decoder and $V$ an optimal plain decoder (the published decoders of the mission), and $\mathbf m$ the fixed universal semimeasure on $\mathbb N=\{1,2,\dots\}$.
--
--   1. For $n\in\mathbb N_0$, $K(n)$ and $C(n)$ are the prefix and plain complexities of $n$, coded by the number $n$ itself; for $n\ge1$ they agree with the published complexities of objects.
--   2. For a finite set $\Omega\subseteq\mathbb N$ and an elementary probability measure $Q$, $C(\Omega)$ and $C(Q)$ are their plain complexities, with the published codes.
--   3. Chaitin's busy beaver function and its plain counterpart are
--   $$\mathrm{BB}(s)=\max\{n\in\mathbb N\mid K(n)\le s\},\qquad \mathrm{BB}_C(s)=\max\{n\in\mathbb N\mid C(n)\le s\},$$
--   with $\max\emptyset:=0$.
--   4. The inverse busy beaver function is $\mu(t)=\min\{K(n)\mid n\in\mathbb N,\ n>t\}$ for real $t\ge0$.
--   5. $\sigma(t)=\mathbf m(\{n\in\mathbb N\mid K(n)>t\})$ for real $t\ge0$.
--
--   These quantities enter the bounds of Theorems 5, 6, 9, 11 and the supporting Lemmas 4, 19 and 20.
--
--   **Formalization Note** Complexities take values in $\mathbb N\cup\{\infty\}$ (`ℕ∞`); for optimal decoders they are finite. $\mathrm{BB}$ and $\mathrm{BB}_C$ are `sSup` of a set of natural numbers; the set is finite (fewer than $2^{s+1}$ programs have length at most $s$), so `sSup` is its maximum, and `sSup ∅ = 0` matches $\max\emptyset:=0$. $\mu(t)$ is an infimum in `ℕ∞` over the nonempty set of positive integers $n>t$, hence attained; theorems that use $\mu(t)$ or $K(\alpha)$ as an exponent assert in their conclusion that the value is a natural number.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, p.4 (K, C, N, N0), p.6 eqs. (4)–(5) and the definition of σ before Lemma 4, p.10 (C(Q)), p.19 (BB_C)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Prefix complexity `K(n)` of a natural number `n ∈ ℕ₀` (S, p.4). The code of `n` is `n`
itself, so for `n ≥ 1` this agrees with the published `Kobj` (whose object code is the
number). For an optimal prefix decoder `K(n)` is finite for every `n`. -/
noncomputable def KNat (U : OptimalPrefixDecoder) (n : ℕ) : ℕ∞ := U.K n noCond

/-- Plain complexity `C(n)` of a natural number `n ∈ ℕ₀`, with the same code `n`. -/
noncomputable def CNat (V : OptimalPlainDecoder) (n : ℕ) : ℕ∞ := V.C n noCond

/-- Plain complexity `C(Ω)` of a finite set `Ω ⊆ ℕ`, with the published set code. -/
noncomputable def Cset (V : OptimalPlainDecoder) (Ω : Finset ℕ+) : ℕ∞ := V.C (setCode Ω) noCond

/-- Plain complexity `C(Q)` of an elementary probability measure, with the published code. -/
noncomputable def Cmeas (V : OptimalPlainDecoder) (Q : ElemMeasure) : ℕ∞ := V.C Q.code noCond

/-- Chaitin's busy beaver function (S, p.6, eq. (4)):
`BB(s) = max{n ∈ ℕ | K(n) ≤ s}`, with `max ∅ = 0`. The set is finite (a prefix-free decoder
has fewer than `2^{s+1}` programs of length at most `s`), so the supremum is a maximum. -/
noncomputable def busyBeaver (U : OptimalPrefixDecoder) (s : ℕ) : ℕ :=
  sSup {n : ℕ | 0 < n ∧ KNat U n ≤ (s : ℕ∞)}

/-- The plain counterpart (S, p.19): `BB_C(s) = max{n ∈ ℕ | C(n) ≤ s}`, with `max ∅ = 0`
(finite set, as above). -/
noncomputable def busyBeaverC (V : OptimalPlainDecoder) (s : ℕ) : ℕ :=
  sSup {n : ℕ | 0 < n ∧ CNat V n ≤ (s : ℕ∞)}

/-- The inverse busy beaver function (S, p.6, eq. (5)): `µ(t) = min{K(n) | n ∈ ℕ, n > t}`
for real `t`. The infimum over the nonempty set of positive integers `n > t` is attained
in `ℕ∞`; it is finite since every `K(n)` is finite. -/
noncomputable def invBusyBeaver (U : OptimalPrefixDecoder) (t : ℝ) : ℕ∞ :=
  ⨅ (n : ℕ+) (_ : t < ((n : ℕ) : ℝ)), Kobj U n

/-- `σ(t) = m({n ∈ ℕ | K(n) > t})` (S, p.6). -/
noncomputable def sigma (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (t : ℝ) : ℝ :=
  mass m {n : ℕ+ | (t : EReal) < toEReal (Kobj U n)}

end UniversalNonstochastic.Main.Supplement


