-- Prove2me | Definitions.Def_ResistantSets_circuitVerts
-- name    : ResistantSets_circuitVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:21.097352+00:00
-- url     : https://prove2.me/theorems/74bb2a40-24e1-4ae5-ae11-3bcf962b666a
-- title:
--   Straight circuit $(v : i_1,\dots,i_\ell)$ and its vertex set
-- statement:
--   Take a point $v\in\{0,1\}^n$, an integer $\ell\in\{2,\dots,n\}$ and distinct coordinates $i_1,\dots,i_\ell$. The **straight circuit** $(v : i_1,\dots,i_\ell)$ is the circuit
--   $$
--   (v_0,v_1,\dots,v_\ell,\dots,v_{2\ell-1},v_{2\ell}=v_0)
--   $$
--   of $G_n$ with $v_0=v$, $v_j=v_{j-1}\triangle e_{i_j}$ and $v_{\ell+j}=v_{\ell+j-1}\triangle e_{i_j}$ for $j\in[\ell]$. Equivalently $v_j=v\triangle\chi_{\{i_1,\dots,i_j\}}$ and $v_{\ell+j}=v\triangle\chi_{\{i_{j+1},\dots,i_\ell\}}$. Its length (number of edges) is $2\ell$, and $V(K)$ denotes its vertex set; $K\triangle x$ is the circuit with vertices $V(K)\triangle x$. A circuit of $G_n[\overline S]$ is **infeasible**. The circuit $(\mathbf 0:1,2,\dots,n-1)$ uses the coordinates $1,\dots,n-1$ in order.
--
--   Straight infeasible circuits of length $2(n-1)$ in the hyperplane $\{x : x_n=0\}$ are the configuration analysed in §5.
--
--   **Formalization Note** The circuit enters statements through its vertex set `circuitVerts v ι`, its length $2\ell$ (the length of `ι`) and the condition `IsStraightCircuit ι` ($\ell\ge2$, distinct coordinates). `stdSeq n` is the sequence $(1,\dots,n-1)$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, pp.22–23, §5 (straight circuit, length of a circuit, feasible/infeasible circuit, footnote 7)

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsStraightInfeasiblePath

namespace ResistantSets

/-- The set `{i_{j+1}, …, i_ℓ}` of the coordinates of `ι = (i₁, …, i_ℓ)` after the first `j`
(0-indexed positions `p ≥ j`). -/
def seqSuffix {n ℓ : ℕ} (ι : Fin ℓ → Fin n) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun p : Fin ℓ => j ≤ p.val).image ι

/-- A coordinate sequence `(i₁, …, i_ℓ)` defines a **straight circuit** when `ℓ ∈ {2, …, n}` and
the coordinates are distinct (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §5, pp.22–23). -/
def IsStraightCircuit {n ℓ : ℕ} (ι : Fin ℓ → Fin n) : Prop :=
  2 ≤ ℓ ∧ Function.Injective ι

/-- The coordinate sequence `(1, 2, …, n − 1)` of the circuit `(0 : 1, 2, …, n − 1)`; paper
coordinate `j` is the index `j − 1`. -/
def stdSeq (n : ℕ) : Fin (n - 1) → Fin n := fun p => ⟨p.val, by have := p.isLt; omega⟩

/-- **Vertex set `V(K)` of the straight circuit `K = (v : i₁, …, i_ℓ)`** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §5,
pp.22–23): "Take a point v ∈ {0,1}ⁿ, an integer ℓ ∈ {2, …, n}, and distinct coordinates
i₁, …, i_ℓ ∈ [n]. Denote by (v : i₁, i₂, …, i_ℓ) the circuit (v₀, v₁, …, v_ℓ, …, v_{2ℓ−1},
v_{2ℓ} = v₀) where v₀ = v and v_j = v_{j−1}△e_{i_j} and v_{ℓ+j} = v_{ℓ+j−1}△e_{i_j} for each
j ∈ [ℓ]."

So `v_j = v △ χ{i₁, …, i_j}` and `v_{ℓ+j} = v △ χ{i_{j+1}, …, i_ℓ}` for `0 ≤ j ≤ ℓ`; the circuit
has length `2ℓ`.

**Formalization Note** The circuit enters every statement only through its vertex set, its
length `2ℓ` (the length of `ι`) and the requirement `IsStraightCircuit ι`. An infeasible
circuit (a circuit of `Gₙ[S̄]`, p.23) is one with `V(K) ∩ S = ∅`; `V(K△x)` (footnote 7, p.23)
is `{w △ x : w ∈ V(K)}`. -/
def circuitVerts {n ℓ : ℕ} (v : Fin n → Bool) (ι : Fin ℓ → Fin n) : Finset (Fin n → Bool) :=
  (Finset.range (ℓ + 1)).image (fun j => vxor v (chi (seqPrefix ι j))) ∪
    (Finset.range (ℓ + 1)).image (fun j => vxor v (chi (seqSuffix ι j)))

end ResistantSets


