-- Prove2me | Definitions.Def_FourBlockIP_FPT_Supplement_FairMatching
-- name    : FourBlockIP_FPT_Supplement_FairMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:12.373745+00:00
-- url     : https://prove2.me/theorems/faac212b-3035-4125-859c-9335eb5f94e3
-- title:
--   Max-Min Fair Matching with size constraints — instances, yes-instances, encoding length
-- statement:
--   An **instance** $I$ of Max-Min Fair Matching with size constraints consists of a bipartite graph $G=(U\,\dot\cup\,V,E)$ with finite sides $U=\{0,\dots,|U|-1\}$ and $V=\{0,\dots,k-1\}$, a finite set $\mathcal C=\{0,\dots,|\mathcal C|-1\}$ of colours with a colouring $\mathrm{col}:U\to\mathcal C$, an integer $\ell\ge0$, and two integers $q^-,q^+$ (of any sign). The edge set is given by its adjacency relation $\mathrm{adj}(u,v)$.
--
--   1. **Left-perfect many-to-one matching.** A set $M\subseteq E$ containing exactly one edge at every $u\in U$; equivalently, a map $m:U\to V$ with $\{u,m(u)\}\in E$ for every $u$.
--   2. **Loads and colour counts.** $|M(v)|=|\{u: m(u)=v\}|$ and $|M(v)_c|=|\{u: m(u)=v,\ \mathrm{col}(u)=c\}|$; a colour absent from $M(v)$ has count $0$.
--   3. **$\ell$-fairness (Max-Min).** For every $v\in V$,
--   $$\max_{c\in\mathcal C}|M(v)_c|-\min_{c\in\mathcal C}|M(v)_c|\le\ell,$$
--   both extrema over all of $\mathcal C$; this is stated as $|M(v)_c|-|M(v)_{c'}|\le\ell$ for all $c,c'\in\mathcal C$.
--   4. **Yes-instance.** Some left-perfect many-to-one matching is $\ell$-fair and satisfies $q^-\le|M(v)|\le q^+$ for every $v\in V$.
--   5. **Encoding and encoding length.** $I$ is encoded as the integer list $(|U|,k,|\mathcal C|,\ell,q^-,q^+)$, followed by the colours $0,\dots,|\mathcal C|-1$ of $\mathcal C$, the values $\mathrm{col}(u)$ for $u\in U$, and the $|U|\times k$ adjacency matrix as $0/1$ entries in row-major order. The encoding length $|I|$ is the sum over the list entries $z$ of $\lfloor\log_2|z|\rfloor+2$ for $z\neq0$ and $1$ for $z=0$ (binary length plus a sign bit), so $\ell,q^-,q^+$ count by their bit length.
--
--   These objects carry the statement of Theorem 13, which answers Boehmer and Koana's question for Max-Min fairness.
--
--   **Formalization Note** $|I|$ is written with `Nat.size |z| + 1`. The colour set is listed element by element, as an explicit input set is; the encoding is injective, since the first three entries fix the lengths of the remaining blocks.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Appendix B, problem definition and Theorem 13, p. 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf, SHA-256 6a8c564a99596cb456f614d44bf2506b1e9049dd12482fe67ba426616cf2df21

import Mathlib

namespace FourBlockIP.FPT.Supplement

/-- An instance of Max-Min Fair Matching with size constraints (p. 20).
`U = Fin nU`, `V = Fin k`, the colour set `C = Fin nC`, `col : U → C`,
the edge set `E` of the bipartite graph `G = (U ∪ V, E)` as the adjacency
predicate `adj u v`, the tolerance `ℓ = ell ≥ 0` and the size bounds
`q⁻ = qMinus`, `q⁺ = qPlus` (arbitrary integers). -/
structure FairMatchingInstance where
  nU : ℕ
  k : ℕ
  nC : ℕ
  col : Fin nU → Fin nC
  adj : Fin nU → Fin k → Bool
  ell : ℕ
  qMinus : ℤ
  qPlus : ℤ

namespace FairMatchingInstance

variable (I : FairMatchingInstance)

/-- A left-perfect many-to-one matching `M ⊆ E` (exactly one edge at every `u ∈ U`),
given by the partner map `m : U → V`; every chosen pair `{u, m u}` is an edge. -/
def IsLeftPerfect (m : Fin I.nU → Fin I.k) : Prop :=
  ∀ u, I.adj u (m u) = true

/-- `|M(v)|`: the number of vertices of `U` matched to `v`. -/
def load (m : Fin I.nU → Fin I.k) (v : Fin I.k) : ℕ :=
  (Finset.univ.filter fun u => m u = v).card

/-- `|M(v)_c|`: the number of vertices of colour `c` matched to `v`
(zero when no vertex of colour `c` is matched to `v`). -/
def colorCount (m : Fin I.nU → Fin I.k) (v : Fin I.k) (c : Fin I.nC) : ℕ :=
  (Finset.univ.filter fun u => m u = v ∧ I.col u = c).card

/-- `ℓ`-fairness with respect to Max-Min: `max_{c ∈ C} |M(v)_c| − min_{c ∈ C} |M(v)_c| ≤ ℓ`
for every `v`, both extrema over all of `C`, written as a bound on every pairwise difference. -/
def IsFair (m : Fin I.nU → Fin I.k) : Prop :=
  ∀ v c c', (I.colorCount m v c : ℤ) - (I.colorCount m v c' : ℤ) ≤ (I.ell : ℤ)

/-- Yes-instance: some left-perfect many-to-one matching is `ℓ`-fair and satisfies
`q⁻ ≤ |M(v)| ≤ q⁺` for every `v ∈ V`. -/
def IsYes : Prop :=
  ∃ m : Fin I.nU → Fin I.k, I.IsLeftPerfect m ∧ I.IsFair m ∧
    ∀ v, I.qMinus ≤ (I.load m v : ℤ) ∧ (I.load m v : ℤ) ≤ I.qPlus

/-- Binary instance encoding as an integer list: the six numbers `|U|, |V|, |C|, ℓ, q⁻, q⁺`;
the colour set `C` listed element by element; the colours `col u` for `u ∈ U`;
the adjacency matrix of `G` as 0/1 entries, row-major (`u` outer, `v` inner). -/
def encode : List ℤ :=
  ([(I.nU : ℤ), I.k, I.nC, I.ell, I.qMinus, I.qPlus] : List ℤ) ++
    (List.range I.nC).map (fun c => (c : ℤ)) ++
    List.ofFn (fun u => ((I.col u : ℕ) : ℤ)) ++
    (List.ofFn fun u => List.ofFn fun v => if I.adj u v then (1 : ℤ) else 0).flatten

/-- The encoding length `|I|`: every list entry `z` costs its binary length plus a sign bit,
`Nat.size |z| + 1`. -/
def encLength : ℕ :=
  ((I.encode).map fun z => Nat.size z.natAbs + 1).sum

end FairMatchingInstance

end FourBlockIP.FPT.Supplement


