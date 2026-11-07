-- Prove2me | Definitions.Def_QuantumPRC_recover
-- name    : QuantumPRC_recover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:01.213231+00:00
-- url     : https://prove2.me/theorems/7069e599-a374-45b1-8a0a-341a2aeb065b
-- title:
--   Bipartite graphs, $(t,d)$-good graphs (Definitions 8.1–8.3), BlockRecover and Recover (Constructions 8.5, 8.6)
-- statement:
--   Let $G$ be a simple graph on $[2n]$ with $L=[n]$ and $R=[2n]\setminus[n]$.
--
--   1. $G$ is **bipartite** (Definition 8.1) if every edge joins $L$ and $R$; its **biadjacency matrix** $B\in\mathbb F_2^{n\times n}$ has $B_{x,y}=1$ iff $\{x,n+y\}\in E$.
--   2. For $S\subseteq L$, $T\subseteq R$: $\Gamma_R(S)=\{y\in R : |\{x\in S : B_{x,y-n}=1\}|=1\}$ and $\Gamma_L(T)=\{x\in L : |\{y\in T: B_{x,y-n}=1\}|=1\}$ (Definition 8.2).
--   3. $G$ is **$(t,d)$-good for $v\in\{0,1\}^{2n}$** (Definition 8.3) if it is bipartite and (i) every vertex has degree at most $d$; (ii) for every nonempty $S\subseteq L$, $T\subseteq R$ with $|S|,|T|\le 2t$: $|\Gamma_R(S)|\ge\frac34d|S|$ and $|\Gamma_L(T)|\ge\frac34 d|T|$; (iii) for every $i\in[2n]$: $|\{j : A_{i,j}=1,\ v_j=1\}|\le d/16$.
--   4. **$\mathsf{BlockRecover}_{t,d}(M,e)$** (Construction 8.5): start with $\hat x=0^n$, $r=e$; while fewer than $8t$ flips have been made, compute the scores $\sigma(j)=|\{i : M_{i,j}=1,\ r_i=1\}|$; stop if no $j$ has $\sigma(j)>5d/8$, otherwise flip the smallest such $j$ ($\hat x\leftarrow\hat x\oplus\varepsilon_j$, $r\leftarrow r\oplus M\varepsilon_j$); output $\hat x$.
--   5. **$\mathsf{Recover}(G,e)$** (Construction 8.6): output $0^{2n}$ unless $G$ is bipartite with maximum degree at most $d$; otherwise output $(\hat u_L,\hat u_R)$ with $\hat u_R=\mathsf{BlockRecover}_{t,d}(B,e_L)$ and $\hat u_L=\mathsf{BlockRecover}_{t,d}(B^\top,e_R)$.
--
--   **Formalization Note** Right vertices are named by their index $y-n\in[n]$. Goodness is also defined at $t=0$ or $d=0$ (condition (ii) is vacuous at $t=0$); the theorems that need positive $t,d$ assume them, as Definition 8.3 does. Thresholds are cleared of denominators.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definitions 8.1–8.3, p.54; Constructions 8.5–8.6, p.55; Definition 3.13, p.18

import Mathlib
import Definitions.Def_QuantumPRC_graphUnitary

open Matrix

namespace QuantumPRC

/-- The left vertex `x ∈ L = [n]` of the vertex set `[2n]`. -/
def vL {n : ℕ} (x : Fin n) : Fin (2 * n) := ⟨x.val, by omega⟩

/-- The right vertex `n + y ∈ R = [2n] ∖ [n]` of the vertex set `[2n]`. -/
def vR {n : ℕ} (y : Fin n) : Fin (2 * n) := ⟨n + y.val, by omega⟩

/-- **Bipartite graph**, Definition 8.1, p.54: every edge of `G` has one endpoint in `L = [n]` and
the other in `R = [2n] ∖ [n]`. -/
def IsBipartiteLR {n : ℕ} (G : SimpleGraph (Fin (2 * n))) : Prop :=
  ∀ i j, G.Adj i j → (i.val < n ↔ ¬ j.val < n)

instance {n : ℕ} (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj] :
    Decidable (IsBipartiteLR G) := by
  unfold IsBipartiteLR; infer_instance

/-- The biadjacency matrix `B ∈ 𝔽₂^{n×n}` (Definition 8.1): `B_{x,y} = 1` iff `{x, n + y} ∈ E`. -/
def biadj {n : ℕ} (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj] (x y : Fin n) : Bool :=
  decide (G.Adj (vL x) (vR y))

/-- The degree `deg_G(i) = |{j : {i,j} ∈ E}|` (Definition 3.13, p.18). -/
def degree {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j => G.Adj i j).card

/-- `Γ_R(S) := {y ∈ R : |{x ∈ S : B_{x,y−n} = 1}| = 1}` (Definition 8.2, p.54), with right vertices
named by their index `y − n ∈ [n]`. -/
def gammaR {n : ℕ} (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter fun y => (S.filter fun x => biadj G x y = true).card = 1

/-- `Γ_L(T) := {x ∈ L : |{y ∈ T : B_{x,y−n} = 1}| = 1}` (Definition 8.2, p.54). -/
def gammaL {n : ℕ} (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj] (T : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter fun x => (T.filter fun y => biadj G x y = true).card = 1

/-- **Graph good for a fixed perturbation**, Definition 8.3. Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), p.54: "For positive integers `t, d` and `v ∈ {0,1}^{2n}`, call `G` `(t, d)`-good for
`v` if it is a bipartite graph and the following conditions hold. (i) Degree bound. Every vertex has
degree at most `d`. (ii) Unique-neighbor bound. For every nonempty `S ⊆ L` and `T ⊆ R` with
`|S|, |T| ≤ 2t`, `|Γ_R(S)| ≥ ¾ d|S|` and `|Γ_L(T)| ≥ ¾ d|T|`. (iii) Local-overlap bound. For every
`i ∈ [2n]`, `|{j ∈ [2n] : A_{i,j} = 1, v_j = 1}| ≤ d/16`."

**Formalization Note.** The predicate is also defined for `t = 0` or `d = 0` (the printed
definition requires positive `t, d`; the theorems using it with positive parameters say so). At
`t = 0` condition (ii) is vacuous. The bounds are cleared of denominators. -/
def IsGood {n : ℕ} (t d : ℕ) (v : Bits (2 * n)) (G : SimpleGraph (Fin (2 * n)))
    [DecidableRel G.Adj] : Prop :=
  IsBipartiteLR G ∧
  (∀ i, degree G i ≤ d) ∧
  (∀ S : Finset (Fin n), S.Nonempty → S.card ≤ 2 * t → 3 * d * S.card ≤ 4 * (gammaR G S).card) ∧
  (∀ T : Finset (Fin n), T.Nonempty → T.card ≤ 2 * t → 3 * d * T.card ≤ 4 * (gammaL G T).card) ∧
  (∀ i, 16 * (Finset.univ.filter fun j => G.Adj i j ∧ v j = true).card ≤ d)

/-- Matrix–vector product over `𝔽₂` for a Boolean matrix: `(Mz)_i = ⊕_j M_{i,j} z_j`. -/
def bmv {n : ℕ} (M : Fin n → Fin n → Bool) (z : Bits n) : Bits n :=
  fun i => decide (Odd (Finset.univ.filter fun j => M i j = true ∧ z j = true).card)

/-- The standard basis vector `ε_j`. -/
def unitVec {n : ℕ} (j : Fin n) : Bits n := fun i => decide (i = j)

/-- The score `σ(j) := |{i ∈ [n] : M_{i,j} = 1, r_i = 1}|`, Eq. (196), p.55. -/
def score {n : ℕ} (M : Fin n → Fin n → Bool) (r : Bits n) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun i => M i j = true ∧ r i = true).card

/-- The loop of Construction 8.5 with `fuel` iterations left, current estimate `x̂` and residual `r`:
if no `j` has `σ(j) > 5d/8`, stop and output `x̂`; otherwise flip the smallest such `j`:
`x̂ ← x̂ ⊕ ε_j`, `r ← r ⊕ Mε_j`. -/
def blockLoop {n : ℕ} (d : ℕ) (M : Fin n → Fin n → Bool) : ℕ → Bits n → Bits n → Bits n
  | 0, x, _ => x
  | k + 1, x, r =>
      match (List.finRange n).find? (fun j => decide (5 * d < 8 * score M r j)) with
      | none => x
      | some j => blockLoop d M k (xorB x (unitVec j)) (xorB r fun i => M i j)

/-- **Block recovery `BlockRecover_{t,d}`**, Construction 8.5. Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), p.55: on input `M ∈ 𝔽₂^{n×n}` and `e ∈ {0,1}^n`, start from `x̂ = 0^n`, `r = e`,
`k = 0`; while `k < 8t`, compute the scores `σ_k(j)`, stop if no `j` satisfies `σ_k(j) > 5d/8`, and
otherwise flip the smallest eligible `j` and increase `k`; output `x̂`. -/
def blockRecover {n : ℕ} (t d : ℕ) (M : Fin n → Fin n → Bool) (e : Bits n) : Bits n :=
  blockLoop d M (8 * t) (fun _ => false) e

/-- The pair `(a, b)` as one string of length `2n`: `a` on `L`, `b` on `R`. -/
def joinLR {n : ℕ} (a b : Bits n) : Bits (2 * n) :=
  fun i => if h : i.val < n then a ⟨i.val, h⟩ else b ⟨i.val - n, by omega⟩

/-- **Full phase recovery `Recover`**, Construction 8.6. Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), p.55: "1. On input a graph `G` on `[2n]` and `e ∈ {0,1}^{2n}`, if `G` is not a bipartite
graph as in Definition 8.1 such that `max_{i∈[2n]} deg_G(i) ≤ d`, output `0^{2n}`. 2. Otherwise, parse
`e = (e_L, e_R)` and compute `û_R := BlockRecover_{t,d}(B, e_L)` and `û_L := BlockRecover_{t,d}(B⊤, e_R)`.
Then, compute the two estimates and output `Recover(G, e) := (û_L, û_R)`." -/
def recover {n : ℕ} (t d : ℕ) (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj]
    (e : Bits (2 * n)) : Bits (2 * n) :=
  if IsBipartiteLR G ∧ ∀ i, degree G i ≤ d then
    joinLR (blockRecover t d (fun y x => biadj G x y) (fun j => e (vR j)))
      (blockRecover t d (biadj G) (fun j => e (vL j)))
  else fun _ => false

end QuantumPRC


