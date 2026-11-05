-- Prove2me | Definitions.Def_PancakeHard_Variable
-- name    : PancakeHard_Variable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:46.539025+00:00
-- url     : https://prove2.me/theorems/3c289e1f-a2b4-455f-8c54-b6deb1eae90b
-- title:
--   Definition 6 — the variable gadget $Variable(P,N,p)=(\nu,V,D)$ with $V^1,V^2$
-- statement:
--   Let $p_\Lambda$ and $m$ be fixed, with keys $key_j$ from $Literals(p_\Lambda,m)$. For disjoint subsets $P=\{p_1,\dots,p_q\}$ and $N=\{n_1,\dots,n_{q'}\}$ of $\llbracket 1;m\rrbracket$ and an integer $p$, let $(take,put,G,H)=Hook(p+2)$ and $(E,F)=Fork(p+14)$. Then $Variable(P,N,p)=(\nu,V,D)$ with $\nu=take$,
--   $$V=\langle G,E,key_{p_1},\dots,key_{p_q},put,key_{n_1},\dots,key_{n_{q'}},F,H\rangle,\qquad D=Dock(p+2,p+29),$$
--   and
--   $$V^1=\langle G'',key_{n_1},\dots,key_{n_{q'}},F^1,H''\rangle,\qquad V^2=\langle G'',key_{p_q},\dots,key_{p_1},F^2,H''\rangle .$$
--
--   The gadget simulates a boolean variable $x_i$: the keys indexed by $P$ (resp. $N$) open the locks of the occurrences of $x_i$ (resp. $\neg x_i$), and when $\nu$ reaches the head a choice is made between $P$ and $N$ (Property 9).
--
--   **Formalization Note** The sets $P$, $N$ are given by their enumerations, lists $[p_1,\dots,p_q]$ and $[n_1,\dots,n_{q'}]$, since the order of the keys in $V$, $V^1$, $V^2$ depends on it. The components are `varNu p`, `varV pΛ P N p`, `varD p`, `varV1 pΛ N p`, `varV2 pΛ P p`.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.2, p.13, Definition 6

import Mathlib
import Definitions.Def_PancakeHard_Dock
import Definitions.Def_PancakeHard_Hook
import Definitions.Def_PancakeHard_Fork
import Definitions.Def_PancakeHard_Literals

set_option autoImplicit false

namespace PancakeHard

/-- `ν` of `Variable(P, N, p)` (Definition 6, arXiv:1111.0434v2, §3.2.2, p.13):
`(take, put, G, H) = Hook(p + 2)` and `ν = take`.

**Formalization Note** The page's `p` is an integer, and here it is one (`p : ℤ`): `ν`, `V`, `V¹`, `V²`
have least entry `p + 3`, so `p = −2` and `p = −1` occur in stacks (Property 9.a) although `Hook` and
`Fork` offsets stay natural numbers. Every offset is written `(p + c).toNat`, which is the page's
`p + c` for `p ≥ −2`, the only offsets for which the gadget has positive entries. -/
def varNu (p : ℤ) : ℕ := hookTake (p + 2).toNat

/-- `V` of `Variable(P, N, p)` (Definition 6, p.13), for fixed `p_Λ` (the offset of the Literals
gadget, p.13: "we assume that p_Λ and m are two fixed integers"):
`V = ⟨G, E, key_{p₁}, …, key_{p_q}, put, key_{n₁}, …, key_{n_{q′}}, F, H⟩` with
`(take, put, G, H) = Hook(p + 2)`, `(E, F) = Fork(p + 14)` and `key_j` the keys of
`Literals(p_Λ, m)`.

**Formalization Note** The paper writes the sets `P = {p₁, …, p_q}` and `N = {n₁, …, n_{q′}}`; their
enumeration fixes the order of the keys in `V`, `V¹`, `V²`. Here `P` and `N` are lists `[p₁, …, p_q]`
and `[n₁, …, n_{q′}]` (the enumerations). -/
def varV (pΛ : ℕ) (P N : List ℕ) (p : ℤ) : List ℕ :=
  hookG (p + 2).toNat ++ forkE (p + 14).toNat ++ P.map (litKey pΛ) ++ [hookPut (p + 2).toNat] ++
    N.map (litKey pΛ) ++ forkF (p + 14).toNat ++ hookH (p + 2).toNat

/-- `D` of `Variable(P, N, p)` (Definition 6, p.13): `D = Dock(p + 2, p + 29)`.

**Formalization Note** `D` contains `p + 1`, so on the page it lies in no stack for `p < 0`; here the
first entry is `0` at `p = −1` and at `p = −2`, so the same holds. -/
def varD (p : ℤ) : List ℕ := Dock (p + 2).toNat (p + 29).toNat

/-- `V¹` (Definition 6, p.13): `V¹ = ⟨G″, key_{n₁}, …, key_{n_{q′}}, F¹, H″⟩`. -/
def varV1 (pΛ : ℕ) (N : List ℕ) (p : ℤ) : List ℕ :=
  hookG'' (p + 2).toNat ++ N.map (litKey pΛ) ++ forkF1 (p + 14).toNat ++ hookH'' (p + 2).toNat

/-- `V²` (Definition 6, p.13): `V² = ⟨G″, key_{p_q}, …, key_{p₁}, F², H″⟩` (keys of `P` in reverse
order). -/
def varV2 (pΛ : ℕ) (P : List ℕ) (p : ℤ) : List ℕ :=
  hookG'' (p + 2).toNat ++ P.reverse.map (litKey pΛ) ++ forkF2 (p + 14).toNat ++
    hookH'' (p + 2).toNat

end PancakeHard


