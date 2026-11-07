-- Prove2me | Definitions.Def_LowAccLTC_TannerCode
-- name    : LowAccLTC_TannerCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:31.751191+00:00
-- url     : https://prove2.me/theorems/39e747b9-bbc1-4879-b82b-dfe1f7269b97
-- title:
--   Weighted distances, distance of a code, and induced local codes $C_s$ of $\mathrm{Tan}(X,C_0)$
-- statement:
--   Let $(X,\mu)$ be a weighted pure $r$-partite complex and $\Sigma$ an alphabet. For a set $S$ of top faces (a **view**) and words $f,g$ on the top faces, the **distance on $S$** is the conditional probability of disagreement,
--   $$\mathrm{dist}_S(f,g)=\Pr_{t\sim\mu}[f(t)\neq g(t)\mid t\in S],$$
--   and the distance of $f$ from a code $C$ is $\mathrm{dist}_S(f,C)=\min_{c\in C}\mathrm{dist}_S(f,c)$. A code **has distance at least $\delta$** on $S$ if any two codewords that differ on $S$ disagree on $S$ with probability at least $\delta$.
--
--   Given local codes $C_u\subseteq\Sigma^{\mathrm{star}(u)}$ on the stars of the co-rank-one faces $u\in X\langle r-1\rangle$, the **HDX (Tanner) code** is
--   $$\mathrm{Tan}(X,C_0)=\{f:X\langle r\rangle\to\Sigma \;:\; f|_{\mathrm{star}(u)}\in C_u \text{ for every } u\in X\langle r-1\rangle\},$$
--   and for every face $s$ the **induced local code** is
--   $$C_s=\{h:\mathrm{star}(s)\to\Sigma \;:\; h|_{\mathrm{star}(u)}\in C_u \text{ for every } u\in X\langle r-1\rangle \text{ with } s\subseteq u\}.$$
--   So $C_\emptyset=\mathrm{Tan}(X,C_0)$ and $C_s=\Sigma^{\{s\}}$ for a top face $s$.
--
--   These codes are the objects whose local testability the paper studies; $C_v$ for vertices $v$ is the local code read by the vertex test.
--
--   **Formalization Note** Local words are represented by words on all top faces, compared only on the relevant star. The minimum over an empty code is taken to be $1$ (the largest possible distance); all codes in the paper's theorems are nonempty.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), §2.1 p.13 (PDF p.16), §2.1.1 p.13, Definition 2.17 pp.17–18 (PDF pp.20–21), §3.2 pp.24–25 (PDF pp.27–28)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- Weighted relative distance on a set `S` of top faces: the `μ`-probability, conditioned on
`S`, that `f` and `g` disagree (§2.1.1, p.13: "Distances are probabilities of disagreement with
respect to these measures"; §3.2, p.25: distances on `star(s)` use `μ` conditioned on
containing `s`). -/
noncomputable def wdist (S : Finset T) (f g : T → A) : ℝ := by
  classical exact (∑ t ∈ S.filter (fun t => f t ≠ g t), X.μ t) / X.mass S

/-- Distance of `f` from a code `C` on the view `S`: `min_{c ∈ C} dist_S(f, c)` (§2.1.1, p.13).

**Formalization Note.** The minimum is taken over the finite set of attained distances together
with the value `1`; since every distance is at most `1`, this is the minimum when `C` is nonempty,
and it is `1` (the largest possible distance) when `C = ∅`. -/
noncomputable def distTo (S : Finset T) (f : T → A) (C : Set (T → A)) : ℝ :=
  sInf (insert 1 ((fun c => X.wdist S f c) '' C))

/-- The code `C` (on the view `S`) has distance at least `δ`: any two codewords that differ on
`S` disagree on `S` with probability at least `δ` (§2.1, p.13, used with lower-bound semantics:
"has distance at least δ"). -/
def HasDistAtLeast (S : Finset T) (C : Set (T → A)) (δ : ℝ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, (∃ t ∈ S, c t ≠ c' t) → δ ≤ X.wdist S c c'

/-- A local code `C ⊆ A^S` on a view `S`, seen as the set of words on all top faces whose
restriction to `S` lies in `C` (values outside `S` are unconstrained). -/
def liftCode (S : Finset T) (C : Set (S → A)) : Set (T → A) :=
  {h | (fun x : S => h x.1) ∈ C}

/-- The induced local code `C_s` of the HDX (Tanner) code `Tan(X, C₀)` (Definition 2.17,
pp.17–18, and §3.2, p.24): the words on `star(s)` whose restriction to `star(u)` lies in `C₀(u)`
for every co-rank-one face `u ⊇ s`. Here `C₀ u ⊆ A^{star(u)}` is the local code on the star of the
co-rank-one face `u` (only its values at faces `u` of size `r - 1` are used).

**Formalization Note.** Local words are represented by words on all top faces; only their values
on `star(s)` matter, and every notion built on `localCode` (distances, agreement) reads only
those values. For a top face `s` there is no constraint, so `C_s` is all words, as in §3.2. -/
def localCode (C₀ : (u : Finset V) → Set (X.star u → A)) (s : Finset V) : Set (T → A) :=
  {h | ∀ u, X.IsFace u → u.card + 1 = r → s ⊆ u → (fun x : X.star u => h x.1) ∈ C₀ u}

/-- The HDX (Tanner) code `Tan(X, C₀) = C_∅` (Definition 2.17, p.18). -/
def tanner (C₀ : (u : Finset V) → Set (X.star u → A)) : Set (T → A) := X.localCode C₀ ∅

end PartiteComplex

end LowAccLTC


