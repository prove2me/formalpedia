-- Prove2me | Definitions.Def_GyoriLovasz_IsWitness
-- name    : GyoriLovasz_IsWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:57.536693+00:00
-- url     : https://prove2.me/theorems/5c0168d0-001b-4a13-902a-bc78ea0919c3
-- title:
--   Flow-essential assignment and the Flow-Essential Assignment Condition
-- statement:
--   Let $c_t\in\mathbb N$ be a capacity for each terminal $t\in T$. An **assignment** is a map $\varphi:V\setminus T\to T$ (Definition 3.4), with $\varphi^{-1}(t)=\{v\in V\setminus T:\varphi(v)=t\}$. It is a **flow-essential assignment** (a witness) if
--
--   1. for every $v\in V\setminus T$, the terminal $\varphi(v)$ is essential for $v$; and
--   2. for every $t\in T$, $|\varphi^{-1}(t)|=c_t$.
--
--   $G$ satisfies the **Flow-Essential Assignment Condition** if a flow-essential assignment exists.
--
--   **Formalization Note** $\varphi$ and $c$ are total functions on the ambient vertex type; only $\varphi$ on $V\setminus T$ and $c$ on $T$ are read. That $\varphi(v)\in T$ is part of essentiality.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 3.4 and Definition 1.2, p.20

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential

namespace GyoriLovasz

/-- **Flow-essential assignment (a witness).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 3.4 and Definition 1.2, p.20: "(1) for every
vertex v ∈ V \ T, the terminal φ(v) is essential for v; and (2) for every terminal t ∈ T, we have
|φ⁻¹(t)| = c_t."

**Formalization Note.** `φ : V → V` and `c : V → ℕ` are total; only `φ` on `V \ T` and `c` on `T` are read.
`φ(v) ∈ T` is part of `IsEssential`. -/
def IsWitness {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ) (φ : V → V) : Prop :=
  (∀ v ∈ G.verts \ T, IsEssential G T v (φ v)) ∧
    ∀ t ∈ T, ((G.verts \ T).filter fun v => φ v = t).card = c t

/-- **The Flow-Essential Assignment Condition.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 1.2, p.20: "We say that G satisfies the
Flow-Essential Assignment Condition if there exists an assignment φ such that" `IsWitness` holds. -/
def FEAC {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ) : Prop :=
  ∃ φ : V → V, IsWitness G T c φ

end GyoriLovasz


