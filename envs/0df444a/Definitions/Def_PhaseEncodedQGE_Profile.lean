-- Prove2me | Definitions.Def_PhaseEncodedQGE_Profile
-- name    : PhaseEncodedQGE_Profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:52.338703+00:00
-- url     : https://prove2.me/theorems/e42188f0-58aa-418e-bf8f-9f0bd7908f5e
-- title:
--   Profiles $q^{\mathrm{in}},q^{\mathrm{out}}$, extremal counts $E_{\mathrm{in}},E_{\mathrm{out}}$, odd readings, their histograms over $m$-subsets, and the mixer profiles $h^{X,r},h^Y$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices and $D$ a set of vertices, with $k_j(D)=|N(j)\cap D|$.
--
--   1. The **profile** of $D$ is the pair of count vectors, for $k=0,1,2,3$,
--   $$q^{\mathrm{in}}_k(D)=\#\{j\in D:k_j(D)=k\},\qquad q^{\mathrm{out}}_k(D)=\#\{j\notin D:k_j(D)=k\}.$$
--   2. The **extremal counts** are $E_{\mathrm{in}}(D)=q^{\mathrm{in}}_0+q^{\mathrm{in}}_3$ and $E_{\mathrm{out}}(D)=q^{\mathrm{out}}_0+q^{\mathrm{out}}_3$.
--   3. The **odd readings** are $(q_3-q_0,\;q_2-q_1)$ for each of the two count vectors.
--   4. The **extremal-count histogram** of $G$ at level $m$ is the multiset of pairs $(E_{\mathrm{in}}(D),E_{\mathrm{out}}(D))$ over all $m$-subsets $D\subseteq V(G)$, and the **odd-reading histogram** is the multiset of the two odd readings over the same subsets.
--   5. The **mixer profiles** are, for $k\in\{0,1,2,3\}$,
--   $$h^{X,r}(k)=\sum_{b=1}^{r}\cos\bigl(b\gamma(2k-3)\bigr),\qquad h^{Y}(k)=\sin\bigl(\gamma(2k-3)\bigr).$$
--
--   The histograms are the graph invariants that the sorted readout is shown to determine; the mixer profiles are the weights of the first-order template.
--
--   **Formalization Note** Histograms are multisets (multiplicities count) indexed by `powersetCard m`. Odd readings are integer pairs. In $h^{X,r}$ and $h^Y$ the integer $k$ is cast to $\mathbb R$ before $2k-3$ is formed, so there is no truncated subtraction.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.5 (PDF p.6), eqs. (3)–(4); §3.1, p.6 (PDF p.7), eq. (8); App. A.1, p.13 (PDF p.14), eqs. (18)–(19); Theorem A, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_GraphNbhd
set_option autoImplicit false

namespace PhaseEncodedQGE

open Classical in
/-- The inside count vector `q^in_k(D) = #{j ∈ D : k_j(D) = k}` of the profile of a defect set `D`
(Miller, Lee, STOC 2027 submission (build 2026-11-03), §2, p.5, eq. (3); eq. (18), p.13). -/
noncomputable def qin {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) (k : ℕ) : ℕ :=
  (D.filter (fun j => kdef G D j = k)).card

open Classical in
/-- The outside count vector `q^out_k(D) = #{j ∉ D : k_j(D) = k}` (eq. (3), p.5). -/
noncomputable def qout {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) (k : ℕ) : ℕ :=
  ((Finset.univ \ D).filter (fun j => kdef G D j = k)).card

/-- The profile of `D`: the pair of count vectors `(q^in_k(D))_{k=0..3}` and `(q^out_k(D))_{k=0..3}`
(eq. (3), p.5; eq. (18), p.13). -/
noncomputable def profile {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) :
    (Fin 4 → ℕ) × (Fin 4 → ℕ) :=
  (fun k => qin G D k, fun k => qout G D k)

/-- The inside extremal count `E_in(D) = q^in_0 + q^in_3` (eq. (4), p.5). -/
noncomputable def Ein {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : ℕ :=
  qin G D 0 + qin G D 3

/-- The outside extremal count `E_out(D) = q^out_0 + q^out_3` (eq. (4), p.5). -/
noncomputable def Eout {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : ℕ :=
  qout G D 0 + qout G D 3

/-- The inside odd reading `(q^in_3 − q^in_0, q^in_2 − q^in_1)` (§2, p.5), in `ℤ × ℤ`. -/
noncomputable def oddIn {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : ℤ × ℤ :=
  ((qin G D 3 : ℤ) - qin G D 0, (qin G D 2 : ℤ) - qin G D 1)

/-- The outside odd reading `(q^out_3 − q^out_0, q^out_2 − q^out_1)` (§2, p.5), in `ℤ × ℤ`. -/
noncomputable def oddOut {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : ℤ × ℤ :=
  ((qout G D 3 : ℤ) - qout G D 0, (qout G D 2 : ℤ) - qout G D 1)

/-- The histogram of the extremal counts `(E_in(D), E_out(D))` over all `m`-subsets `D ⊆ V(G)`, as a
multiset (multiplicities count) (Theorem A, p.2; Theorem A.8, p.15). -/
noncomputable def extremalHist {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Multiset (ℕ × ℕ) :=
  ((Finset.univ : Finset (Fin n)).powersetCard m).val.map (fun D => (Ein G D, Eout G D))

/-- The histogram of the odd readings `((q_3 − q_0, q_2 − q_1)^in, (q_3 − q_0, q_2 − q_1)^out)` over
all `m`-subsets `D ⊆ V(G)`, as a multiset (Theorem A, p.2; Theorem A.21, p.21). -/
noncomputable def oddHist {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) :
    Multiset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard m).val.map (fun D => (oddIn G D, oddOut G D))

/-- The X-mixer profile `h^{X,r}(k) = ∑_{b=1}^{r} cos(bγ(2k − 3))` for `r` tied repetitions
(§3.1, p.6, eq. (8); eq. (23), p.14).

**Formalization Note** `k` is a natural number cast to `ℝ` before `2k − 3` is formed, so there is no
truncated subtraction. -/
noncomputable def hX (r : ℕ) (γ : ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 r, Real.cos ((b : ℝ) * γ * (2 * (k : ℝ) - 3))

/-- The Y-mixer profile `h^Y(k) = sin(γ(2k − 3))` (§3.1, p.6, eq. (8); eq. (24), p.14). -/
noncomputable def hY (γ : ℝ) (k : ℕ) : ℝ := Real.sin (γ * (2 * (k : ℝ) - 3))

end PhaseEncodedQGE


