-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Certificates
-- name    : BatchedFacilityLocation_Nonuniform_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:34.133895+00:00
-- url     : https://prove2.me/theorems/eff826ba-3c8f-439f-8f21-9ef23b923816
-- title:
--   Keys, certified charges, first certificates and the progress quantities
-- statement:
--   This file defines the analysis objects of §4.1 and §4.4 for a fixed center $c$, whose level $j_C$ is that of $f_C=\hat f(c)$.
--
--   **Keys and certification.** For a client $v$ and level $j$, the static key (4.3) is
--   $$Z_v^{(j)}=d(c,v)+d_v^{(j)}+f_jU_v^{(j)},$$
--   set to $\infty$ if $d_v^{(j)}+f_jU_v^{(j)}>d_v^{(j-1)}$. The pair $(v,j)$ is *certified* if its key is finite and $Z_v^{(j)}\le d(c,F_v)$, and *regularly certified* if moreover $Z_v^{(j)}\le d(c,M_j)+f_j$.
--
--   **Charges.** $Y_v=\sum_{j\le j_C}f_j\mathbf 1\{(v,j)\text{ certified}\}$. For a set $C$ of clients and a batch $b$, with $C_b=C\cap b$,
--   $$W_b=\sum_{j\le j_C}f_j\mathbf 1\{\exists v\in C_b:(v,j)\text{ certified}\},\qquad W_C=\sum_bW_b.$$
--   $K_C^{(j)}$ is the number of batches containing a level-$j$ certification from $C$, and $L_C^{(j)}$ the number containing a regular one.
--
--   **Progress quantities.** $q_j(F)=[d(c,F)-d(c,M_j)]_+$ with $q_j(\emptyset)=\infty$, and $\xi_v^{(j)}=d(c,v)+d_v^{(j)}-d(c,M_j)$, a real number.
--
--   Each notion is defined once for a single client facing an arbitrary open set $F$, and then along the execution with $F=F_v$.
--
--   **Formalization Note** $q_j$ uses truncated subtraction in $[0,\infty]$, which is the positive part; $\xi$ is real, so its sign is a genuine claim.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §4.1 p. 14 (key (4.3), certification, Y_v, W_b, W_C); §4.4 p. 20 (K_C^(j), L_C^(j), regular certification, q_j, xi_v^(j))

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Algorithm

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

noncomputable section

open Classical

/-! # Keys, certified charges and first certificates

§4.1 p. 14 (key (4.3), certification, `Y_v`, `W_b`, `W_C`) and §4.4 p. 20 (`K_C^{(j)}`,
`L_C^{(j)}`, regular certification, `q_j`, `ξ_v^{(j)}`). A center `c` is fixed; its level is
`j_C`, the level of rounded cost `f_C = f̂(c)`, so "`j ≤ j_C`" reads `f_j ≤ f̂(c)`. -/

variable {S : Type*} [Fintype S] [MetricSpace S]

/-! ## One client, facing a given open set `F` -/

/-- The static key (4.3) of the client-level pair (client at site `x`, level `j`):
`Z = d(c, v) + d_v^{(j)} + f_j U_v^{(j)}`, set to `∞` if `d_v^{(j)} + f_j U_v^{(j)} > d_v^{(j-1)}`. -/
def key (f : S → ℝ) (c x : S) (u : Lev f → ℝ) (t : Lev f) : ℝ≥0∞ :=
  if dset x (Mset f t) + ENNReal.ofReal ((t : ℝ) * u t) ≤ dset x (MsetLt f t) then
    ENNReal.ofReal (dist c x) + dset x (Mset f t) + ENNReal.ofReal ((t : ℝ) * u t)
  else ⊤

/-- `(v, j)` is certified (against center `c`, pre-client open set `F`): its key is finite and
`Z_v^{(j)} ≤ d(c, F_v)`. -/
def certStep (f : S → ℝ) (c : S) (F : Finset S) (x : S) (u : Lev f → ℝ) (t : Lev f) : Prop :=
  key f c x u t < ⊤ ∧ key f c x u t ≤ dset c F

/-- Regular certification (p. 20): certified and `Z_v^{(j)} ≤ d(c, M_j) + f_j`. -/
def regCertStep (f : S → ℝ) (c : S) (F : Finset S) (x : S) (u : Lev f → ℝ) (t : Lev f) :
    Prop :=
  certStep f c F x u t ∧ key f c x u t ≤ dset c (Mset f t) + ENNReal.ofReal (t : ℝ)

/-- `Y_v = Σ_{j ≤ j_C} f_j 1{(v, j) is certified}`. -/
def Ystep (f : S → ℝ) (c : S) (F : Finset S) (x : S) (u : Lev f → ℝ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.univ.filter (fun t : Lev f => (t : ℝ) ≤ fhat f c),
    ENNReal.ofReal (t : ℝ) * (if certStep f c F x u t then 1 else 0)

/-- `q_j(F) = [d(c, F) - d(c, M_j)]_+`, with `q_j(∅) = ∞` (truncated subtraction in `[0, ∞]`). -/
def qexc (f : S → ℝ) (c : S) (t : Lev f) (F : Finset S) : ℝ≥0∞ :=
  dset c F - dset c (Mset f t)

/-- `ξ_v^{(j)} = d(c, v) + d_v^{(j)} - d(c, M_j)`, a real number (`M_j` is nonempty). -/
def xi (f : S → ℝ) (c x : S) (t : Lev f) : ℝ :=
  dist c x + Metric.infDist x (Mset f t : Set S) - Metric.infDist c (Mset f t : Set S)

/-! ## Along the single-copy execution on an instance -/

variable (tb : TieBreak S) (f : S → ℝ) (I : Instance S) (c : S)

/-- `(i, j)` is certified in the execution: certification against the actual `F_v`. -/
def certified (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ)
    (i : Fin I.n) (t : Lev f) : Prop :=
  certStep f c (Fpre tb f I σ τ U i) (I.loc i) (U i) t

/-- `(i, j)` is regularly certified in the execution. -/
def regCertified (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (U : Fin I.n → Lev f → ℝ) (i : Fin I.n) (t : Lev f) : Prop :=
  regCertStep f c (Fpre tb f I σ τ U i) (I.loc i) (U i) t

/-- `Y_v` of client `i` in the execution. -/
def Y (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ)
    (i : Fin I.n) : ℝ≥0∞ :=
  Ystep f c (Fpre tb f I σ τ U i) (I.loc i) (U i)

/-- `W_b = Σ_{j ≤ j_C} f_j 1{∃ v ∈ C_b : (v, j) is certified}`, `C_b = C ∩ b`. -/
def Wb (C : Finset (Fin I.n)) (b : Fin I.B) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.univ.filter (fun t : Lev f => (t : ℝ) ≤ fhat f c),
    ENNReal.ofReal (t : ℝ) *
      (if ∃ i ∈ C, I.batch i = b ∧ certified tb f I c σ τ U i t then 1 else 0)

/-- `W_C = Σ_b W_b`. -/
def WC (C : Finset (Fin I.n)) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ∑ b, Wb tb f I c C b σ τ U

/-- `K_C^{(j)}`: the number of batches containing a level-`j` certification from `C`. -/
def KC (C : Finset (Fin I.n)) (t : Lev f) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ((Finset.univ.filter (fun b : Fin I.B =>
      ∃ i ∈ C, I.batch i = b ∧ certified tb f I c σ τ U i t)).card : ℝ≥0∞)

/-- `L_C^{(j)}`: the number of batches containing a regular level-`j` certification from `C`. -/
def LC (C : Finset (Fin I.n)) (t : Lev f) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ((Finset.univ.filter (fun b : Fin I.B =>
      ∃ i ∈ C, I.batch i = b ∧ regCertified tb f I c σ τ U i t)).card : ℝ≥0∞)

end

end BatchedFacilityLocation.Nonuniform


