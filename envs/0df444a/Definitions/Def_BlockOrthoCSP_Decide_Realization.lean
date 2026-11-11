-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Realization
-- name    : BlockOrthoCSP_Decide_Realization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:05.757686+00:00
-- url     : https://prove2.me/theorems/9f10773a-6067-48ad-9442-643a57e3cbfc
-- title:
--   The row-equivalence detector $C_n$ (F.54) and relations defined by equality-free pp-formulas
-- statement:
--   For a constraint language $\mathcal F$, $F : D^{j+1} \to \mathbb C$ and $t \ge 0$, put $n = 1 + tL_q$ and
--   $$C_n(x,y) = \sum_{z\in D} F(x,z)^{(e_K-1)n}\, F(y,z)^n \qquad (F.54)$$
--   on concatenated tuples $(x,y) \in D^{j}\times D^{j}$ (arity $2(r-1)$, no conjugation).
--
--   For members $F_1,\dots,F_h$ of $W_{\mathcal F}$, free variables $x \in D^\ell$, existential variables $y \in D^s$, and atoms $e$ (finitely many) each with an index $i(e)$ and an ordered scope $z_e$ over the $\ell + s$ variables (repeats allowed), the defined relation is
--   $$R(x) \iff \exists y \ \bigwedge_e \Phi_{F_{i(e)}}(z_e).$$
--   `ppCode` lists the atoms as (index, scope variable numbers).
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-30, Lemma F.7.2; p. F-36, Eq. (F.54)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_NumberField

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-- The row-equivalence detector (F.54), p. F-36, for `F : D^{j+1} → ℂ` and `n = 1 + t L_q`:
`C_n(x, y) = ∑_{z ∈ D} F(x, z)^{(e_K − 1) n} F(y, z)^n`, a function of the concatenation
`(x, y) ∈ D^{j + j}` (arity `2(r − 1)`). No complex conjugation. -/
noncomputable def detector {q j : ℕ} (F : Finset (CFn q)) (t : ℕ)
    (G : (Fin (j + 1) → Fin q) → ℂ) : (Fin (j + j) → Fin q) → ℂ :=
  fun w => ∑ z : Fin q,
    G (Fin.snoc (fun i => w (Fin.castAdd j i)) z) ^ ((eK F - 1) * (1 + t * Lq q)) *
      G (Fin.snoc (fun i => w (Fin.natAdd j i)) z) ^ (1 + t * Lq q)

/-- The relation defined by an equality-free pp-formula over generated supports
(Lemma F.7.2, p. F-30): free variables `x ∈ D^ℓ`, existential variables `y ∈ D^s`, atoms
`e ∈ Fin nE` with function index `i(e) ∈ [h]` and scope `z_e` (entries among the `ℓ + s`
variables, repeats allowed): `R(x) ⟺ ∃ y, ⋀_e Φ_{F_{i(e)}}(z_e)`. -/
def ppRel {q h ℓ s nE : ℕ} (Fs : Fin h → CFn q) (idx : Fin nE → Fin h)
    (scope : (e : Fin nE) → Fin (Fs (idx e)).1 → Fin (ℓ + s)) : Set (Fin ℓ → Fin q) :=
  {x | ∃ y : Fin s → Fin q, ∀ e, (Fs (idx e)).2 (Fin.append x y ∘ scope e) ≠ 0}

/-- The code of such a formula's atoms: `(i(e), z_e)` with variable numbers. -/
def ppCode {q h ℓ s nE : ℕ} (Fs : Fin h → CFn q) (idx : Fin nE → Fin h)
    (scope : (e : Fin nE) → Fin (Fs (idx e)).1 → Fin (ℓ + s)) : List (ℕ × List ℕ) :=
  List.ofFn fun e => ((idx e : ℕ), List.ofFn fun p => (scope e p : ℕ))

end BlockOrthoCSP.Decide


