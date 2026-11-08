-- Prove2me | Definitions.Def_WICanon_WCScheme
-- name    : WICanon_WCScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:39.25619+00:00
-- url     : https://prove2.me/theorems/bdb28de2-3e94-4822-9c83-2b8cc4f911b0
-- title:
--   Witness canonicalization schemes ($\varepsilon$-WC)
-- statement:
--   An **$\varepsilon$-witness canonicalization scheme** for an NP relation $\mathcal R$ is a pair $(\mathrm{map},V)$ of deterministic polynomial-time algorithms with public randomness $r\in\{0,1\}^{\ell(|x|)}$, $\ell$ polynomial, such that:
--
--   1. **Completeness:** $\Pr_r[V(r,x,\mathrm{map}(r,x,w))=1]\ge 1-\mathrm{negl}(|x|)$ for $(x,w)\in\mathcal R$.
--   2. **Soundness:** for $x\notin\mathcal L(\mathcal R)$, an adversary finds an accepted $\pi$ with probability at most $\mathrm{negl}(|x|)$. The adversary is non-uniform PPT (computational soundness) or unbounded (statistical soundness).
--   3. **Uniqueness:** for every $x$ there is a family $\{\pi_{x,r}\}_r$ such that $\Pr_r[\mathrm{map}(r,x,w)=\pi_{x,r}]\ge 1-\varepsilon$ for every witness $w$ of $x$.
--
--   **Perfect** completeness means $V(r,x,\mathrm{map}(r,x,w))=1$ for every $r$; **perfect** soundness means $V(r,x,\pi)=0$ for every $x\notin\mathcal L(\mathcal R)$, every $r$ and every $\pi$. In a **non-uniform** scheme both algorithms have polynomial-length advice per instance length.
--
--   **Formalization Note** The family $\pi_{x,r}$ is chosen before $w$. The polynomial-time clause carries the notion: for arbitrary functions, the least witness would give a perfect scheme for every relation. The computational adversary also receives $x$, which with advice per length loses nothing, and statistical soundness uses the strongest adversary, one who finds an accepted $\pi$ whenever it exists.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.13, p.15; p.30

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_WICanon_IsNPRelation

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ OWFLocalDesc

/-- **A witness canonicalization scheme as raw data** (Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…,
Definition 2.13, p.15): the pair `(map, V)` and the polynomial `ℓ` of its public randomness. -/
structure WCScheme where
  map : Str → Str → Str → Str
  verify : Str → Str → Str → Bool
  ℓ : Polynomial ℕ

namespace WCScheme

/-- `map` and `V` are deterministic polynomial-time algorithms (Definition 2.13, p.15). Without this
clause a perfect scheme would exist for every relation, by `map` = the least witness. -/
def Uniform (S : WCScheme) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ r x w, g (tup [r, x, w]) = S.map r x w) ∧
  ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ r x π, g (tup [r, x, π]) = bitStr (S.verify r x π)

/-- A non-uniform scheme: "both the map map and the verifier V have access to polynomial-length
non-uniform advice" (Definition 2.13, p.15), one advice string per instance length. -/
def NonUniform (S : WCScheme) : Prop :=
  ∃ (a : ℕ → Str) (p : Polynomial ℕ) (g h : Str → Str),
    (∀ n, (a n).length ≤ p.eval n) ∧ PolyTimeComputable g ∧ PolyTimeComputable h ∧
    (∀ r x w, g (tup [a x.length, r, x, w]) = S.map r x w) ∧
    ∀ r x π, h (tup [a x.length, r, x, π]) = bitStr (S.verify r x π)

/-- Completeness (Definition 2.13, p.15), with one negligible error for all `(x, w) ∈ R`. -/
def Complete (S : WCScheme) (R : Relation) : Prop :=
  ∃ α : ℕ → ℝ, Negligible α ∧ ∀ x w, R x w →
    1 - α x.length ≤ avgCoins (S.ℓ.eval x.length) fun r =>
      if S.verify r x (S.map r x w) = true then 1 else 0

/-- Computational soundness (Definition 2.13, p.15), in the asymptotic form of `SoundCompNegl`: for
each non-uniform PPT adversary one negligible error at all `x ∉ L(R)`.

**Formalization Note.** Printed, the adversary is `A(r)`. Here it also receives `x`. With per-length
advice alone it could not read the instance; hardwiring the worst instance of each length in the
advice gives the same notion. -/
def SoundComp (S : WCScheme) (R : Relation) : Prop :=
  ∀ A : NUPPT, ∃ β : ℕ → ℝ, Negligible β ∧ ∀ x, ¬ InLang R x →
    (avgCoins (S.ℓ.eval x.length) fun r =>
      A.expect x.length (pair x r) fun π => if S.verify r x π = true then 1 else 0) ≤ β x.length

open Classical in
/-- Statistical soundness (Definition 2.13, p.15: "if the above holds even when A is inefficient"):
the strongest inefficient adversary finds an accepted `π` whenever one exists (as on p.31). -/
def SoundStat (S : WCScheme) (R : Relation) : Prop :=
  ∃ β : ℕ → ℝ, Negligible β ∧ ∀ x, ¬ InLang R x →
    (avgCoins (S.ℓ.eval x.length) fun r =>
      if ∃ π, S.verify r x π = true then 1 else 0) ≤ β x.length

/-- Perfect completeness (p.30): "V(r, x, map(r, x, w)) = 1 for every (x, w) ∈ R and every public
random string r". -/
def PerfectComplete (S : WCScheme) (R : Relation) : Prop :=
  ∀ x w r, R x w → r.length = S.ℓ.eval x.length → S.verify r x (S.map r x w) = true

/-- Perfect soundness (p.30): "V(r, x, π) = 0 for every x ∉ L(R), every r, and every purported proof
π". -/
def PerfectSound (S : WCScheme) (R : Relation) : Prop :=
  ∀ x r π, ¬ InLang R x → r.length = S.ℓ.eval x.length → S.verify r x π = false

/-- Uniqueness with error `ε` (Definition 2.13, p.15): for every `x` there is a family `π_{x,r}`,
fixed before the witness, with `Pr_r[map(r, x, w) = π_{x,r}] ≥ 1 − ε(|x|)` for every witness `w`. -/
def Unique (S : WCScheme) (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∀ x, ∃ π : Str → Str, ∀ w, R x w →
    1 - ε x.length ≤ avgCoins (S.ℓ.eval x.length) fun r =>
      if S.map r x w = π r then 1 else 0

end WCScheme

/-- `R` has an `ε`-WC (computationally sound) (Definition 2.13, p.15; Theorem 3.3). -/
def HasWC (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∃ S : WCScheme, S.Uniform ∧ S.Complete R ∧ S.SoundComp R ∧ S.Unique R ε

/-- `R` has a statistically sound `ε`-WC (Definition 2.13, p.15; Theorem 3.3, Lemma 3.24). -/
def HasStatWC (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∃ S : WCScheme, S.Uniform ∧ S.Complete R ∧ S.SoundStat R ∧ S.Unique R ε

/-- `R` has an `ε`-WC with perfect completeness and perfect statistical soundness (Theorem 3.25,
Lemma 3.24). -/
def HasPerfectWC (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∃ S : WCScheme, S.Uniform ∧ S.PerfectComplete R ∧ S.PerfectSound R ∧ S.Unique R ε

/-- The non-uniform form of `HasStatWC` (Lemma 3.24, last sentence). -/
def HasStatWCNonUniform (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∃ S : WCScheme, S.NonUniform ∧ S.Complete R ∧ S.SoundStat R ∧ S.Unique R ε

/-- The non-uniform form of `HasPerfectWC` (Lemma 3.24, last sentence). -/
def HasPerfectWCNonUniform (R : Relation) (ε : ℕ → ℝ) : Prop :=
  ∃ S : WCScheme, S.NonUniform ∧ S.PerfectComplete R ∧ S.PerfectSound R ∧ S.Unique R ε

end WICanon


