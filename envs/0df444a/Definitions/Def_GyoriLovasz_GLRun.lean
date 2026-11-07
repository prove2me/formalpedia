-- Prove2me | Definitions.Def_GyoriLovasz_GLRun
-- name    : GyoriLovasz_GLRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:56.546218+00:00
-- url     : https://prove2.me/theorems/9f8cb5f2-034a-4f40-bd31-a5b32ca2b572
-- title:
--   Runs of GLPartition (Algorithm 2)
-- statement:
--   A **run** of Algorithm 2 on $(G,T,c,\varphi)$ with $n$ recursive calls returning parts $\langle V_t\rangle$ is built from the four branches of the algorithm, in the printed order:
--
--   1. (lines 1–2) $G$ has no vertices: return empty parts.
--   2. (lines 3–8) some terminal $t$ has $c_t=0$: run on $(G\setminus\{t\},T\setminus\{t\},c,\varphi)$, then set $V_t=\{t\}$.
--   3. (lines 9–15) no capacity is $0$, and some pre-terminal $x$ with $d^+(x)=1$ has the edge $(x,t)$: run on the contraction of $x$ into $t$ with $c_t$ decreased by one, then add $x$ to $V_t$.
--   4. (lines 16–19) neither applies: choose a matching $p$ and secondary edges $e$ (Algorithm 3, lines 1–2), run the while loop of Algorithm 3 to some $\varphi_1$, exit at an $e_t$ non-critical for $\varphi_1$, and run on $(G\setminus e_t,T,c,\varphi_1)$.
--
--   **Formalization Note** Every free choice is an argument. $\varphi\setminus\{v\}$ is the same function read on a smaller vertex set, and $c'$ of line 5 is $c$ read on $T\setminus\{t\}$. "$G=\emptyset$" is read as "no vertices remain" (the comment on line 2).
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Algorithm 2, p.24; Algorithm 3, p.25

import Mathlib
import Definitions.Def_GyoriLovasz_PT
import Definitions.Def_GyoriLovasz_IsTermMatching
import Definitions.Def_GyoriLovasz_ShiftChain

namespace GyoriLovasz

/-- **A run of Algorithm 2 (GLPartition).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Algorithm 2, p.24.
`GLRun G T c φ n parts`: on input `(G, T, c, φ)` the recursion makes `n` recursive calls and returns `parts`.
The four constructors are the printed branches in the printed order, with their guards:

* `empty`: lines 1–2, `G = ∅`;
* `zero`: lines 3–8, some `c_t = 0`: delete `t`, recurse, set `V_t ← {t}`;
* `contract`: lines 9–15, no capacity is `0`, and a pre-terminal `x` has `d⁺(x) = 1` with `(x, t) ∈ E`:
  contract, `c_t ← c_t − 1`, recurse with `φ \ {x}`, set `V_t ← V_t ∪ {x}`;
* `shift`: lines 16–19, neither applies: choose a matching `p` and secondary edges `sec` (Algorithm 3, lines 1–2),
  run the while loop to `φ₁`, exit at a `sec t` non-critical for `φ₁`, delete it and recurse on `φ₁`.

**Formalization Note.** Every choice the algorithm leaves free is a constructor argument, so a statement over all
runs covers all choices. `φ \ {x}` is the same `φ`, since `φ` is only read on the current `V \ T`; `c′` is the
same `c` on the smaller `T`. `G = ∅` is read as "no vertices" (p.24: "No vertices remain"). The guards are
written on `G.verts.Nonempty`, the failure of line 1. -/
inductive GLRun {V : Type*} [DecidableEq V] :
    DG V → Finset V → (V → ℕ) → (V → V) → ℕ → (V → Finset V) → Prop
  | empty {G : DG V} {T : Finset V} {c : V → ℕ} {φ : V → V} (hG : G.verts = ∅) :
      GLRun G T c φ 0 fun _ => ∅
  | zero {G : DG V} {T : Finset V} {c : V → ℕ} {φ : V → V} {n : ℕ} {parts : V → Finset V} {t : V}
      (hG : G.verts.Nonempty) (ht : t ∈ T) (hc : c t = 0)
      (h : GLRun (G.deleteVertex t) (T.erase t) c φ n parts) :
      GLRun G T c φ (n + 1) (Function.update parts t {t})
  | contract {G : DG V} {T : Finset V} {c : V → ℕ} {φ : V → V} {n : ℕ} {parts : V → Finset V}
      {x t : V} (hG : G.verts.Nonempty) (hc : ∀ s ∈ T, c s ≠ 0) (hx : x ∈ PT G T T) (ht : t ∈ T)
      (ha : (x, t) ∈ G.arcs) (hd : G.outDeg x = 1)
      (h : GLRun (G.contract x t) T (Function.update c t (c t - 1)) φ n parts) :
      GLRun G T c φ (n + 1) (Function.update parts t (insert x (parts t)))
  | shift {G : DG V} {T : Finset V} {c : V → ℕ} {φ φ₁ : V → V} {n m : ℕ} {parts : V → Finset V}
      {p : V → V} {sec : V → V × V} {t : V} (hG : G.verts.Nonempty) (hc : ∀ s ∈ T, c s ≠ 0)
      (hd : ∀ x ∈ PT G T T, ∀ s ∈ T, (x, s) ∈ G.arcs → G.outDeg x ≠ 1)
      (hp : IsTermMatching G T p) (hs : IsSecondary G T p sec)
      (hch : ShiftChain G T sec φ m φ₁) (ht : t ∈ T) (hnc : IsNonCritical G T (sec t) φ₁)
      (h : GLRun (G.deleteArc (sec t)) T c φ₁ n parts) : GLRun G T c φ (n + 1) parts

end GyoriLovasz


