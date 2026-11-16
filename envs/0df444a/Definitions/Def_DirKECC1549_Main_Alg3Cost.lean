-- Prove2me | Definitions.Def_DirKECC1549_Main_Alg3Cost
-- name    : DirKECC1549_Main_Alg3Cost
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:14:03.413798+00:00
-- url     : https://prove2.me/theorems/47386028-6e1f-4479-a2cb-cbae18d73b61
-- title:
--   Algorithm 3 with the cost of the proof of Lemma 5
-- statement:
--   Algorithm 3 together with the running-time account of the proof of Lemma 5 (p.18).
--
--   $\mathrm{Alg3CostRun}(n,m,G,k,P,T)$ says that $P$ is the output of a run of Algorithm 3 on $(G,k)$, exactly as in $\mathrm{Alg3Run}$, and that $T$ is the cost of that run. The cost charges every call of the recursion as the proof of Lemma 5 does, with the local work written out:
--
--   - **Base case** (lines 1–2, $k=1$ or $n=1$): $T=k^{3k}(m+n+1)$.
--   - **Not strongly connected** (lines 3–4): $T=k^{3k}(m+n+1)+\sum_S T_S$, summed over the strongly connected components $S$, where $T_S$ is the cost of the run on $G[S]$.
--   - **Main case** (lines 5–14):
--   $$T=k^{3k}(m+n+1)+2^k(k+1)!\,n\,\Delta+(|Z_G|+|Z_{G^R}|)(k+1)(m+n+1)+T_{k-1}+\sum_{z\in Z_G,\,q_z<k}T_z+\sum_{z\in Z_{G^R},\,q_z<k}T_z.$$
--     Here $\Delta=\max\{k-1,\lceil m/n^{\varepsilon_k}\rceil\}$ (line 6), $T_{k-1}$ is the cost of the call on $(G,k-1)$ (line 7), and $T_z$ is the cost of the call on the residual graph $H$ with parameter $k-q_z$ (line 13).
--
--   The term $2^k(k+1)!\,n\Delta$ is the cost of Lemma 1 (p.11). The term $(k+1)(m+n+1)$ per hitting-set vertex covers Lemma 3, which costs $O(k(m+n))$ (p.15), and the $O(n)$ common refinement (p.16). The term $k^{3k}(m+n+1)$ covers the remaining $O(m+n)$ work of a call: strongly connected components, layouts, the hitting sets of Lemma 2 (p.14), and computing $\Delta$.
-- source:
--   Georgiadis, Kipouridis, Kosinas, Papadopoulos, Pergaminelis, STOC 2027 submission #1549, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1549.pdf, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18-19)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main

/-!
# Algorithm 3 with the cost charged in the proof of Lemma 5 (p.18)

`Alg3CostRun n m G k P T` is `Alg3Run n m G k P` together with a cost `T` that charges every
level of the recursion as in the proof of Lemma 5: the local work of a call (strongly connected
components, layouts, Lemma 2, the common refinements) is charged `k^{3k}·(m + n + 1)`, Lemma 1 is
charged `2^k·(k+1)!·n·Δ`, every application of Lemma 3 is charged `(k+1)·(m + n + 1)`, and the
recursive calls add their own costs.
-/

variable {n m : ℕ}

inductive Alg3CostRun :
    (n m : ℕ) → (Fin m → Fin n × Fin n) → ℕ → (Fin n → Fin n → Prop) → ℕ → Prop
  | base {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ) :
      (k = 1 ∨ n = 1) → Alg3CostRun n m G k (StronglyConn G) (k ^ (3 * k) * (m + n + 1))
  | split {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ)
      (runs : (S : Finset (Fin n)) → Fin S.card → Fin S.card → Prop)
      (cost : Finset (Fin n) → ℕ) :
      ¬ (k = 1 ∨ n = 1) → ¬ IsStronglyConnected G →
      (∀ u : Fin n, Alg3CostRun (sccOf G u).card (inducedEdges G (sccOf G u)).card
          (induced G (sccOf G u)) k (runs (sccOf G u)) (cost (sccOf G u))) →
      Alg3CostRun n m G k (fun u v => liftRel (sccOf G u) (runs (sccOf G u)) u v)
        (k ^ (3 * k) * (m + n + 1) + ∑ S ∈ univ.image (sccOf G), cost S)
  | main {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ)
      (Pk1 P : Fin n → Fin n → Prop) (r : Fin n) (ZG ZR : Finset (Fin n))
      (qG qR : Fin n → ℕ) (FG FR : Fin n → Finset (Fin m))
      (QG QR : Fin n → Fin n → Fin n → Prop) (T₀ : ℕ) (TG TR : Fin n → ℕ) :
      ¬ (k = 1 ∨ n = 1) → IsStronglyConnected G →
      Alg3CostRun n m G (k - 1) Pk1 T₀ →
      Lemma1Guarantee G k (alg3Delta n m k) Pk1 P →
      Lemma2Guarantee G r k (alg3Delta n m k) ZG →
      Lemma2Guarantee (Rev G) r k (alg3Delta n m k) ZR →
      (∀ z ∈ ZG, qG z = min k (lam G z r) ∧ IsUnitFlow G (FG z) z r (qG z)) →
      (∀ z ∈ ZG, qG z < k → Alg3CostRun n m (flipEdges G (FG z)) (k - qG z) (QG z) (TG z)) →
      (∀ z ∈ ZR, qR z = min k (lam (Rev G) z r) ∧ IsUnitFlow (Rev G) (FR z) z r (qR z)) →
      (∀ z ∈ ZR, qR z < k →
        Alg3CostRun n m (flipEdges (Rev G) (FR z)) (k - qR z) (QR z) (TR z)) →
      Alg3CostRun n m G k (fun u v => P u v ∧ (∀ z ∈ ZG, qG z < k → QG z u v) ∧
          (∀ z ∈ ZR, qR z < k → QR z u v))
        (k ^ (3 * k) * (m + n + 1) + 2 ^ k * (k + 1).factorial * n * alg3Delta n m k +
          (ZG.card + ZR.card) * (k + 1) * (m + n + 1) + T₀ +
          ∑ z ∈ ZG.filter (fun z => qG z < k), TG z +
          ∑ z ∈ ZR.filter (fun z => qR z < k), TR z)

end DirKECC1549.Main


