-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_IndexMaps
-- name    : MultiplierAssoc206_Resolution_IndexMaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:12:17.550318+00:00
-- url     : https://prove2.me/theorems/c00fbda2-f35a-406f-b063-77614f06711e
-- title:
--   Strip width $g$ and index maps with the collision pattern of Lemma 7.3
-- statement:
--   Let $H=(U,V,E)$ be a bipartite graph with $|V|=m$. The strip width is
--   $$g=\lceil\log_2(m+2)\rceil+2.$$
--   For maps $i:U\to\mathbb N$, $j:E\to\mathbb N$, $k:V\to\mathbb N$ the columns (Definition 7.1) are $\mathrm{col}_{\mathbf{xy}}(u,e)=i(u)+j(e)$, $\mathrm{col}_{\mathbf{yz}}(e,v)=j(e)+k(v)$ and $\mathrm{col}_{(\mathbf{xy})\mathbf z}(u,e,v)=\mathrm{col}_{\mathbf x(\mathbf{yz})}(u,e,v)=i(u)+j(e)+k(v)$; the difference pair of a triple is $\big(i(u)-i(u_e),\,k(v)-k(v_e)\big)\in\mathbb Z^2$. A pair or triple is incident when its vertices are endpoints of $e$.
--
--   **Index maps** for strip width $g$ and bound $n_0$ are maps $i,j,k$ together with columns $\mathrm{col}_{\mathbf{xy}}(v)$ ($v\in V$), $\mathrm{col}_{\mathbf{yz}}(u)$ ($u\in U$) and $K$ satisfying the properties of Lemma 7.3:
--
--   1. (Mapping pattern) $i,j,k$ are injective, take values in multiples of $g$, and $i(u)+j(e)+k(v)<n_0$ for all $u,e,v$;
--   2. (Inner collision pattern) $\mathrm{col}_{\mathbf{xy}}(u_e,e)=\mathrm{col}_{\mathbf{xy}}(v_e)$ for every edge, $v\mapsto\mathrm{col}_{\mathbf{xy}}(v)$ is injective, and the column of each non-incident pair $(u,e)$ differs from the column of every other pair; symmetrically $\mathrm{col}_{\mathbf{yz}}(e,v_e)=\mathrm{col}_{\mathbf{yz}}(u_e)$, $u\mapsto\mathrm{col}_{\mathbf{yz}}(u)$ is injective, and each non-incident pair $(e,v)$ has its own column;
--   3. (Outer collision pattern) two triples have the same outer column if and only if they have the same difference pair; the difference pair is $(0,0)$ exactly for the incident triples $(u_e,e,v_e)$, whose common column is $K$; and a nonzero difference $i(u)-i(u_e)$ (resp. $k(v)-k(v_e)$) determines the ordered pair $(u,u_e)$ (resp. $(v,v_e)$).
--
--   The paper notes (PDF p.17) that the rest of the argument uses only these three properties, so the restriction $\rho$ and Lemmas 7.5–8.7 are stated for any such maps.
--
--   **Formalization Note** The named columns $\mathrm{col}_{\mathbf{xy}}(v)$, $\mathrm{col}_{\mathbf{yz}}(u)$ are part of the data; for a vertex without edges (excluded in §§7–8) the column is otherwise unconstrained. Differences are computed in $\mathbb Z$.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.14–16 (printed pp.13–15), Definition 7.1 (PDF p.14), Lemma 7.3 properties (i)–(iii) (PDF pp.15–16)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Graph

namespace MultiplierAssoc206.Resolution

open Classical

/-! # Index maps and their collision pattern

Liew, *Associativity of Multiplication Is Hard for Resolution*, Definition 7.1 (PDF p. 14) and
the three properties of Lemma 7.3 (PDF pp. 15–16). "The rest of the argument uses only the three
properties of Lemma 7.3" (PDF p. 17), so the maps are packaged as a structure of those
properties; Definition 7.4 and Lemmas 7.5–8.7 take any such maps. -/

/-- The strip width `g = ⌈log₂(m + 2)⌉ + 2` of Lemma 7.3 and Definition 7.4. -/
def stripWidth (m : ℕ) : ℕ := Nat.clog 2 (m + 2) + 2

variable {U V : Type} [Fintype U] [Fintype V]

/-- Index maps `i : U → ℕ`, `j : E → ℕ`, `k : V → ℕ` with the properties (i)–(iii) of
Lemma 7.3 for strip width `g` and bound `n₀`, together with the columns `col_xy(v)`,
`col_yz(u)` and `K` that the lemma names. Definition 7.1: `col_xy(u,e) = i(u) + j(e)`,
`col_yz(e,v) = j(e) + k(v)`, `col_(xy)z(u,e,v) = col_x(yz)(u,e,v) = i(u) + j(e) + k(v)`; the
difference pair of `(u, e, v)` is `(i(u) − i(u_e), k(v) − k(v_e))`, computed in `ℤ`. -/
structure IndexMaps (E : Finset (U × V)) (g n₀ : ℕ) where
  /-- x-bit-positions of the vertices of `U` -/
  i : U → ℕ
  /-- y-bit-positions of the edges -/
  j : Edge E → ℕ
  /-- z-bit-positions of the vertices of `V` -/
  k : V → ℕ
  /-- the column `col_xy(v)` shared by the incident pairs `(u_e, e)`, `e ∈ E(v)` -/
  cxy : V → ℕ
  /-- the column `col_yz(u)` shared by the incident pairs `(e, v_e)`, `e ∈ E(u)` -/
  cyz : U → ℕ
  /-- the common outer column `K` of the incident triples -/
  K : ℕ
  /-- (i) the maps are injective -/
  i_inj : Function.Injective i
  j_inj : Function.Injective j
  k_inj : Function.Injective k
  /-- (i) the maps take values in multiples of `g` -/
  i_dvd : ∀ u, g ∣ i u
  j_dvd : ∀ e, g ∣ j e
  k_dvd : ∀ v, g ∣ k v
  /-- (i) `i(u) + j(e) + k(v) < n₀` -/
  lt_n₀ : ∀ u e v, i u + j e + k v < n₀
  /-- (ii)(a) the incident pairs `(u_e, e)` with `e ∈ E(v)` share the column `col_xy(v)` -/
  xy_common : ∀ e : Edge E, i e.1.1 + j e = cxy e.1.2
  /-- (ii)(a) distinct vertices `v` have distinct columns `col_xy(v)` -/
  cxy_inj : Function.Injective cxy
  /-- (ii)(a) each non-incident pair `(u, e)` occupies its own column -/
  xy_own : ∀ (u : U) (e : Edge E), u ≠ e.1.1 →
    ∀ (u' : U) (e' : Edge E), (u', e') ≠ (u, e) → i u' + j e' ≠ i u + j e
  /-- (ii)(b) the incident pairs `(e, v_e)` with `e ∈ E(u)` share the column `col_yz(u)` -/
  yz_common : ∀ e : Edge E, j e + k e.1.2 = cyz e.1.1
  /-- (ii)(b) distinct vertices `u` have distinct columns `col_yz(u)` -/
  cyz_inj : Function.Injective cyz
  /-- (ii)(b) each non-incident pair `(e, v)` occupies its own column -/
  yz_own : ∀ (e : Edge E) (v : V), v ≠ e.1.2 →
    ∀ (e' : Edge E) (v' : V), (e', v') ≠ (e, v) → j e' + k v' ≠ j e + k v
  /-- (iii) the outer column depends only on the difference pair, and distinct difference pairs
  give distinct columns -/
  outer_iff : ∀ (u : U) (e : Edge E) (v : V) (u' : U) (e' : Edge E) (v' : V),
    i u + j e + k v = i u' + j e' + k v' ↔
      (((i u : ℤ) - i e.1.1, (k v : ℤ) - k e.1.2) =
        ((i u' : ℤ) - i e'.1.1, (k v' : ℤ) - k e'.1.2))
  /-- (iii)(a) the triples with difference pair `(0, 0)` are exactly the incident triples -/
  zero_iff : ∀ (u : U) (e : Edge E) (v : V),
    (((i u : ℤ) - i e.1.1, (k v : ℤ) - k e.1.2) = (0, 0)) ↔ (u = e.1.1 ∧ v = e.1.2)
  /-- (iii)(a) their common column is `K` -/
  K_spec : ∀ e : Edge E, i e.1.1 + j e + k e.1.2 = K
  /-- (iii)(b) a nonzero `i`-difference determines its ordered pair of vertices -/
  diffU_unique : ∀ (u : U) (e : Edge E) (u' : U) (e' : Edge E),
    (i u : ℤ) - i e.1.1 = (i u' : ℤ) - i e'.1.1 → (i u : ℤ) - i e.1.1 ≠ 0 →
      u = u' ∧ e.1.1 = e'.1.1
  /-- (iii)(b) a nonzero `k`-difference determines its ordered pair of vertices -/
  diffV_unique : ∀ (v : V) (e : Edge E) (v' : V) (e' : Edge E),
    (k v : ℤ) - k e.1.2 = (k v' : ℤ) - k e'.1.2 → (k v : ℤ) - k e.1.2 ≠ 0 →
      v = v' ∧ e.1.2 = e'.1.2

end MultiplierAssoc206.Resolution


