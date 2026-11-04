-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPairs
-- name    : Submission_Weighted_Global_TernaryArenaPrefixPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T18:10:52.05083+00:00
-- url     : https://prove2.me/theorems/3206e02b-839e-4e3d-9615-0b203d3e82c3
-- title:
--   Ternary Arena Prefix Pairs
-- statement:
--   Definitions and structural lemmas for Ternary Arena Prefix Pairs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPairs.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixGroups
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_fin
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
import Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
import Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
import Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
import Theorems.Thm_ThreeSum_BlockIndex_coordEquiv_val
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_card
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_subset
import Theorems.Thm_ThreeSum_BlockIndex_indexSet_union
import Theorems.Thm_ThreeSum_BlockIndex_index_unindex
import Theorems.Thm_ThreeSum_BlockIndex_mem_indexSet
import Theorems.Thm_ThreeSum_BlockIndex_unindex_index
import Theorems.Thm_ThreeSum_BlockRows_flat_row
import Theorems.Thm_ThreeSum_BlockRows_mem_flat
import Theorems.Thm_ThreeSum_BlockRows_mem_join
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_BlockRows_row_flat
import Theorems.Thm_ThreeSum_BlockRows_row_inter
import Theorems.Thm_ThreeSum_BlockRows_row_join
import Theorems.Thm_ThreeSum_BlockRows_row_sdiff
import Theorems.Thm_ThreeSum_BlockRows_row_union
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_cost
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_program_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sourceArgs_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_source_length
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sources_length
import Theorems.Thm_ThreeSum_LightTernaryWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedRows_program_length
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_program_length
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_zero
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_callArgs_cost
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_source_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sources_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_LocalGraph_endpoint_injective
import Theorems.Thm_ThreeSum_LocalGraph_left_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_right_mem_vertices
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySourceHostModel_mem_records
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
import Theorems.Thm_ThreeSum_WantedPairs_count_zero
import Theorems.Thm_ThreeSum_WantedPairs_pairs_zero
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_hash
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_occurrence
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_pair_encoding_injective
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_hash
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_occurrence
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_block_mem
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_group_code
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_Q
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_group_spec
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_original_rows
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_word_spec
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_left_input
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSetup_setup_right_input
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_block_encodeBlock
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_block_mem
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_dictionary_native
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_left_lt
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_right_lt
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_sourceConfig_config
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mapCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_mem_records
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_raws_length
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_wordCodes_length
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_output
import Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_right
import Theorems.Thm_ThreeSum_WeightedGlobalNativePairAccess_mem_pair
import Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_adds
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_equiv_val
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.BlockCoefficientRows.mapRow_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockEncoding.leftSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.rightSubset_fromSubsets
attribute [local simp] ThreeSum.BlockEncoding.row_leftSubset
attribute [local simp] ThreeSum.BlockEncoding.row_outputSubset
attribute [local simp] ThreeSum.BlockEncoding.row_rightSubset
attribute [local simp] ThreeSum.BlockIndex.coordEquiv_val
attribute [local simp] ThreeSum.BlockIndex.indexSet_card
attribute [local simp] ThreeSum.BlockIndex.indexSet_subset
attribute [local simp] ThreeSum.BlockIndex.indexSet_union
attribute [local simp] ThreeSum.BlockIndex.index_unindex
attribute [local simp] ThreeSum.BlockIndex.mem_indexSet
attribute [local simp] ThreeSum.BlockIndex.unindex_index
attribute [local simp] ThreeSum.BlockRows.flat_row
attribute [local simp] ThreeSum.BlockRows.mem_flat
attribute [local simp] ThreeSum.BlockRows.mem_join
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.BlockRows.row_flat
attribute [local simp] ThreeSum.BlockRows.row_inter
attribute [local simp] ThreeSum.BlockRows.row_join
attribute [local simp] ThreeSum.BlockRows.row_sdiff
attribute [local simp] ThreeSum.BlockRows.row_union
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightTernaryCountFrontend.program_length
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightTernaryGroupedBanks.program_length
attribute [local simp] ThreeSum.LightTernaryMomentChannelStep.callArgs_cost
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
attribute [local simp] ThreeSum.LightTernaryNearSetup.program_length
attribute [local simp] ThreeSum.LightTernaryPreparedWanted.program_length
attribute [local simp] ThreeSum.LightTernaryRequesterMatrix.program_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.args_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.callArgs_cost
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.program_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.sourceArgs_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.source_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.sources_length
attribute [local simp] ThreeSum.LightTernaryWantedQuery.program_length
attribute [local simp] ThreeSum.LightTernaryWantedRows.program_length
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.program_length
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedFrozenQuery.queryTime_zero
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.args_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.callArgs_cost
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.program_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.source_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.sources_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length
attribute [local simp] ThreeSum.LightWeightedWantedRows.program_length
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.Switch.mem_candidates
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
attribute [local simp] ThreeSum.TernarySourceHostModel.mem_records
attribute [local simp] ThreeSum.TernaryWantedBatchIndex.cells_length
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
attribute [local simp] ThreeSum.WantedPairs.count_zero
attribute [local simp] ThreeSum.WantedPairs.pairs_zero
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedFrontendResources.sourceConfig_config
attribute [local simp] ThreeSum.WeightedGlobalArenaSourceSetup.setup_left_input
attribute [local simp] ThreeSum.WeightedGlobalArenaSourceSetup.setup_right_input
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedGlobalFrontendResources.sourceConfig_config
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mapCodes_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.mem_records
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.raws_length
attribute [local simp] ThreeSum.WeightedGlobalGoodOutputCatalog.wordCodes_length
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_output
attribute [local simp] ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
attribute [local simp] ThreeSum.WeightedGlobalNativePairAccess.mem_pair
attribute [local simp] ThreeSum.WeightedGlobalTupleDictionaryDecode.equiv_val
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalArenaPrefixPairs
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup TernaryExtensionEncoding TernaryCanonicalDictionaries
open WeightedGlobalNativePrefixLineage WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPairModel
open TernaryFixedDictionaries
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F Λ r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
abbrev S := setup (r := r) maps τ cap Q (input I L R row root r)
variable {maps τ cap I L R row root Q}
def pair (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count)
    (x : WeightedGlobalNativePairMoments.Pair (S (r := r) maps τ cap I L R row root Q) j.val) :
    (M maps τ cap I L R row root).Pair (group maps τ cap I L R row root r j) :=
  ⟨((⟨x.val.1.1,WeightedGlobalCompactPairedSupport.native_left_lt x⟩,
      ⟨x.val.2.1,WeightedGlobalCompactPairedSupport.native_right_lt x⟩),edge j.isLt x),by
    intro t
    refine ⟨rfl,?_,?_,?_,?_⟩
    · obtain ⟨i,hi,h⟩ := WeightedGlobalArenaSourceModel.original_rows maps cap (input I L R row root r)
        false (fun b t => row t.val (fun a => (L b a : ZMod p))) (by intros; rfl) _ (left_mem x)
      have he : i=leftIndex x := Fin.ext hi
      rw [he] at h
      exact (congrFun h t).trans (left_hash j.isLt x t)
    · obtain ⟨i,hi,h⟩ := WeightedGlobalArenaSourceModel.original_rows maps cap (input I L R row root r)
        true (fun c t => row t.val (fun a => (R c a : ZMod p))) (by intros; rfl) _ (right_mem x)
      have he : i=rightIndex x := Fin.ext hi
      rw [he] at h
      exact (congrFun h t).trans (right_hash j.isLt x t)
    · have hm := WeightedGlobalCanonicalSourceBank.block_mem false maps cap (leftIndex x) t
      have hk : keepLeft maps cap (WeightedGlobalCanonicalSourceBank.block false maps cap (leftIndex x) t).1
          (WeightedGlobalCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val := by
        simpa [records,trimmedLeftRecords,acceptedLeft,keepLeft,leftNative] using hm
      have ho := congrFun (left_occurrence j.isLt x) t
      rw [ho] at hk
      exact hk
    · have hm := WeightedGlobalCanonicalSourceBank.block_mem true maps cap (rightIndex x) t
      have hk : keepRight maps cap (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).1
          (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val := by
        simpa [records,trimmedRightRecords,acceptedRight,keepRight,rightNative] using hm
      have ho := congrFun (right_occurrence j.isLt x) t
      rw [ho] at hk
      exact hk⟩
theorem pair_injective (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :
    Function.Injective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j) := by
  intro x y he
  apply pair_encoding_injective j.isLt
  have hh := congrArg Subtype.val he
  apply Prod.ext
  · exact Prod.ext (congrArg (fun z => z.1.1.val) hh) (congrArg (fun z => z.1.2.val) hh)
  · exact congrArg (fun z : (Fin I.nB×Fin I.nC)×(Fin r→ActualEdge m) => z.2) hh
theorem pair_surjective (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :
    Function.Surjective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j) := by
  intro y
  let out := (group maps τ cap I L R row root r j).val.2
  let ls : Fin r→SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) :=
    fun t => ((out t).1,⟨left (y.val.2 t),left_mem_vertices _⟩)
  let rs : Fin r→SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) :=
    fun t => ((out t).1,⟨right (y.val.2 t),right_mem_vertices _⟩)
  have hls (t : Fin r) : ls t∈records (α := fixedAlpha m) false maps cap := by
    have hh := (y.property t).2.2.2.1
    change WeightedGlobalArenaPrefixGroups.keepLeft maps cap (out t).1 (left (y.val.2 t)) at hh
    simpa [records,trimmedLeftRecords,acceptedLeft,WeightedGlobalArenaPrefixGroups.keepLeft,leftNative,ls] using hh
  have hrs (t : Fin r) : rs t∈records (α := fixedAlpha m) true maps cap := by
    have hh := (y.property t).2.2.2.2
    change WeightedGlobalArenaPrefixGroups.keepRight maps cap (out t).1 (right (y.val.2 t)) at hh
    simpa [records,trimmedRightRecords,acceptedRight,WeightedGlobalArenaPrefixGroups.keepRight,rightNative,rs] using hh
  let il := WeightedGlobalCanonicalSourceBank.encodeBlock false maps cap ls hls
  let ir := WeightedGlobalCanonicalSourceBank.encodeBlock true maps cap rs hrs
  have hbl : WeightedGlobalCanonicalSourceBank.block false maps cap il=ls :=
    WeightedGlobalCanonicalSourceBank.block_encodeBlock false maps cap ls hls
  have hbr : WeightedGlobalCanonicalSourceBank.block true maps cap ir=rs :=
    WeightedGlobalCanonicalSourceBank.block_encodeBlock true maps cap rs hrs
  let I' := input I L R row root r
  let host := S (r := r) maps τ cap I L R row root Q
  have hlkey : host.left.input y.val.1.1.val=
      LightTernarySourceHost.dictionary host.left.xs p r il.val := by
    change (coefficientCode (fun t : Fin r => row t.val (fun a => (L y.val.1.1.val a : ZMod p))) : ℤ)=
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) false maps cap).map (native false maps)) p r il.val
    rw [WeightedGlobalCanonicalSourceBank.dictionary_native false maps cap il]
    congr 1
    congr 1
    funext t
    change row t.val (fun a => (L y.val.1.1.val a : ZMod p))=leftNative maps
      (WeightedGlobalCanonicalSourceBank.block false maps cap il t)
    rw [hbl]
    exact (y.property t).2.1
  have hrkey : host.right.input y.val.1.2.val=
      LightTernarySourceHost.dictionary host.right.xs p r ir.val := by
    change (coefficientCode (fun t : Fin r => row t.val (fun a => (R y.val.1.2.val a : ZMod p))) : ℤ)=
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) true maps cap).map (native true maps)) p r ir.val
    rw [WeightedGlobalCanonicalSourceBank.dictionary_native true maps cap ir]
    congr 1
    congr 1
    funext t
    change row t.val (fun a => (R y.val.1.2.val a : ZMod p))=rightNative maps
      (WeightedGlobalCanonicalSourceBank.block true maps cap ir t)
    rw [hbr]
    exact (y.property t).2.2.1
  have hgl : host.left.group il.val=host.front.group j.val := by
    change (source (r := r) maps cap I' false).group il.val=
      (TernaryWantedBatchIndex.get (entries (r := r) maps τ I') j.val).2.2
    rw [WeightedGlobalArenaSourceModel.group_spec maps cap I' false il,hbl]
    exact (WeightedGlobalArenaQueryModel.group_code maps τ I'.targets I'.positions I'.requesterCount j).symm
  have hgr : host.right.group ir.val=host.front.group j.val := by
    change (source (r := r) maps cap I' true).group ir.val=
      (TernaryWantedBatchIndex.get (entries (r := r) maps τ I') j.val).2.2
    rw [WeightedGlobalArenaSourceModel.group_spec maps cap I' true ir,hbr]
    exact (WeightedGlobalArenaQueryModel.group_code maps τ I'.targets I'.positions I'.requesterCount j).symm
  have hlword : host.front.E.word (host.left.key il.val)=WeightedGlobalRepeatedWords.canonical (fun t => left (y.val.2 t)) := by
    change (WeightedBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I' false).key il.val)=_
    rw [WeightedGlobalArenaSourceModel.word_spec maps cap I' false il]
    change WeightedGlobalRepeatedWords.canonical (fun t => (WeightedGlobalCanonicalSourceBank.block false maps cap il t).2.val)=_
    rw [hbl]
  have hrword : host.front.E.word (host.right.key ir.val)=WeightedGlobalRepeatedWords.canonical (fun t => right (y.val.2 t)) := by
    change (WeightedBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I' true).key ir.val)=_
    rw [WeightedGlobalArenaSourceModel.word_spec maps cap I' true ir]
    change WeightedGlobalRepeatedWords.canonical (fun t => (WeightedGlobalCanonicalSourceBank.block true maps cap ir t).2.val)=_
    rw [hbr]
  have hq : host.front.Q j.val=WeightedGlobalRepeatedWords.canonical (fun t => output (y.val.2 t)) := by
    rw [WeightedGlobalArenaQueryModel.setup_Q j.isLt]
    change WeightedGlobalRepeatedWords.canonical (fun t => (out t).2.val)=_
    apply congrArg WeightedGlobalRepeatedWords.canonical
    funext t
    exact (y.property t).1.symm
  have hp : ((y.val.1.1.val,il.val),(y.val.1.2.val,ir.val))∈WeightedGlobalNativePairMoments.pairs host j.val := by
    apply (WeightedGlobalNativePairAccess.mem_pair _ _ _ _ _ _).mpr
    refine ⟨?_,hgl,?_,hgr,?_⟩
    · apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
      refine ⟨y.val.1.1.isLt,?_,?_⟩
      · change il.val<((records (α := fixedAlpha m) false maps cap).map (native false maps)).length^r
        simpa only [List.length_map] using il.isLt
      · rw [hlkey]
        change ((p^r : ℕ) : ℤ)∣LightTernarySourceHost.dictionary host.left.xs p r il.val-
          LightTernarySourceHost.dictionary host.left.xs p r il.val
        rw [sub_self]; exact dvd_zero _
    · apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
      refine ⟨y.val.1.2.isLt,?_,?_⟩
      · change ir.val<((records (α := fixedAlpha m) true maps cap).map (native true maps)).length^r
        simpa only [List.length_map] using ir.isLt
      · rw [hrkey]
        change ((p^r : ℕ) : ℤ)∣LightTernarySourceHost.dictionary host.right.xs p r ir.val-
          LightTernarySourceHost.dictionary host.right.xs p r ir.val
        rw [sub_self]; exact dvd_zero _
    · rw [hlword,hrword,hq]
      exact WeightedGlobalRepeatedWords.canonical_adds _ _ _ (fun t => (edge_data (y.val.2 t)).2.2.2)
  let x : WeightedGlobalNativePairMoments.Pair host j.val := ⟨_,hp⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext <;> rfl
  funext t
  apply endpoint_injective (fixedAlpha m) (fixedPi m)
  have hixl : leftIndex x=il := rfl
  have hixr : rightIndex x=ir := rfl
  apply Prod.ext
  · change (WeightedGlobalCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val=left (y.val.2 t)
    rw [hixl,hbl]
  · change (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val=right (y.val.2 t)
    rw [hixr,hbr]
def pairEquiv (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :=
  Equiv.ofBijective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j)
    ⟨pair_injective j,pair_surjective j⟩
end ThreeSum.WeightedGlobalArenaPrefixPairs


