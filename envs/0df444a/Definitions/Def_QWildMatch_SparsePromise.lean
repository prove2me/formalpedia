-- Prove2me | Definitions.Def_QWildMatch_SparsePromise
-- name    : QWildMatch_SparsePromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:16:11.884179+00:00
-- url     : https://prove2.me/theorems/c7d315e0-3d43-437c-b509-cf5210c94353
-- title:
--   The sparse-defect promise, the defect list $\mathrm{List}_b$, and reconstruction
-- statement:
--   For every block $b$ a reference $B_b:J_b\to\Sigma$ is given. The defects of block $b$ are $\{x\in J_b:T[x]\ne B_b[x]\}$, and the promise (Assumption 6.1) says that for every $b<N_B$ there are at most $q$ of them; it is global across blocks. The canonical list $\mathrm{List}_b$ records the defects with their true text symbols. Reconstruction from $B_b$ and a list returns the recorded symbol at a listed position and $B_b[x]$ otherwise.
--
--   **Formalization Note** The reference is an arbitrary function, `B b : Fin n → Sym`. Assumption 6.1 calls it periodic, but every function on a finite interval is periodic with period the interval's length and §6 never uses a period; values off $J_b$ play no role. The list is the `Finset` of pairs $(x,T[x])$: the page's sorted order, count register and zero padding to capacity $q$ are one encoding of this set, and a `Finset` is canonical by construction.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Assumption 6.1, p.8; §6.2, p.8; §6.3, pp.9–10

import Mathlib
import Definitions.Def_QWildMatch_J

namespace QWildMatch

/-- The defect set `{x ∈ J_b : T[x] ≠ B_b[x]}`, the support of `g_b` (Zhao et al., STOC 2027
submission, §6.2, p.8).

**Formalization Note** `B b` is the reference of block `b`. It is an arbitrary function: Assumption
6.1 calls `B_b : J_b → Σ` periodic, but every function on a finite interval is periodic with period
its length, and §6 never uses a period. Values of `B b` off `J_b` play no role. -/
def defects {Sym : Type} [DecidableEq Sym] (n L l : ℕ) (B : ℕ → Fin n → Sym) (b : ℕ)
    (T : Fin n → Sym) : Finset (Fin n) :=
  (J n L l b).filter (fun x => T x ≠ B b x)

/-- Assumption 6.1 (Zhao et al., STOC 2027 submission, p.8): the promise is global across blocks; in
each block the text differs from the reference at no more than `q` positions of `J_b`. -/
def SparsePromise {Sym : Type} [DecidableEq Sym] (n L l q : ℕ) (B : ℕ → Fin n → Sym)
    (T : Fin n → Sym) : Prop :=
  ∀ b < NB n L, (defects n L l B b T).card ≤ q

/-- The canonical `List_b` (Zhao et al., STOC 2027 submission, §6.2, p.8): the defects with their
true text symbols.

**Formalization Note** It is the set of pairs `(x, T[x])`. The page's sorted order, count register
and zero padding up to capacity `q` are one encoding of this same set, and a `Finset` is canonical by
construction. -/
def defectList {Sym : Type} [DecidableEq Sym] (n L l : ℕ) (B : ℕ → Fin n → Sym) (b : ℕ)
    (T : Fin n → Sym) : Finset (Fin n × Sym) :=
  (defects n L l B b T).image (fun x => (x, T x))

open Classical in
/-- Reconstruction from `B_b` and a list (Zhao et al., STOC 2027 submission, §6.3, pp.9–10): return
the recorded symbol at a listed position, and `B_b[x]` otherwise. -/
noncomputable def recon {Sym : Type} {n : ℕ} (B : ℕ → Fin n → Sym) (b : ℕ)
    (D : Finset (Fin n × Sym)) : Fin n → Sym :=
  fun x => if h : ∃ a, (x, a) ∈ D then Classical.choose h else B b x

end QWildMatch


